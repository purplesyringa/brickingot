#![cfg_attr(false, no_std)]
#![feature(associated_type_defaults, substr_range)]

extern crate alloc;

mod ast;
mod class;
mod exceptions;
mod high_level;
mod linear;
mod preparse;
mod stackless;
mod structured;
mod utils;

use crate::ast::Arena;
use crate::class::ClassInfo;
use crate::exceptions::parse_try_blocks;
use crate::high_level::decompile_cf_constructs;
use crate::linear::linearize_ir;
use crate::preparse::{BytecodePreparsingError, build_preparse_ir};
use crate::stackless::{StacklessIrError, build_stackless_ir};
use crate::structured::structure_control_flow;
use noak::{
    AccessFlags, MStr,
    descriptor::MethodDescriptor,
    error::DecodeError,
    reader::{Class, Method, attributes::Code, cpool::ConstantPool},
};
use std::time::Instant;
use thiserror::Error;
use tikv_jemallocator::Jemalloc;

#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

#[derive(Debug, Error)]
enum ClassDecompileError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("In method `{name}`: {error}")]
    Method {
        name: String,
        error: MethodDecompileError,
    },
}

#[derive(Debug, Error)]
pub enum MethodDecompileError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("While pre-parsing bytecode: {0}")]
    BytecodePreparsing(#[from] BytecodePreparsingError),

    #[error("While building stackless IR: {0}")]
    StacklessIr(#[from] StacklessIrError),
}

fn decompile_class_file(raw_bytes: &[u8]) -> Result<(), ClassDecompileError> {
    let class = Class::new(raw_bytes)?;
    let pool = class.pool();

    // let bootstrap_methods: Vec<BootstrapMethod> = match class
    //     .attributes()
    //     .find_attribute::<BootstrapMethods>(pool)?
    // {
    //     Some(methods) => methods.methods().iter().collect::<Result<_, _>>()?,
    //     None => Vec::new(),
    // };

    // TODO: issue a diagnostic if ACC_SUPER is unset

    let mut class_info = ClassInfo::new(&class);

    for method in class.methods() {
        let method = method?;
        decompile_method(pool, &method, &mut class_info).map_err(|error| {
            ClassDecompileError::Method {
                name: pool
                    .retrieve(method.name())
                    .unwrap_or(MStr::from_mutf8(b"??").unwrap())
                    .display()
                    .to_string(),
                error,
            }
        })?;
    }

    Ok(())
}

fn decompile_method<'code>(
    pool: &ConstantPool<'code>,
    method: &Method<'code>,
    class_info: &mut ClassInfo<'code>,
) -> Result<(), MethodDecompileError> {
    let Some(code): Option<Code> = method.attributes().find_attribute(pool)? else {
        // No Code attribute, valid e.g. for abstract methods
        return Ok(());
    };

    // println!("method {}", pool.retrieve(method.name())?.display());

    // During the course of decompilation, the program is translated between different IR forms.
    // They are all similar to each other and use the same underlying data structures to represent
    // basic statements (i.e. those without control flow) and expressions in the form of an AST.
    // However, each IR adds a twist, like adding goto's, blocks, or allowing arbitrarily nested
    // expressions.
    //
    // This makes translation between IRs relatively free of boilerplate, but we have to pay for
    // allocation to support expression nesting on each stage, even for IRs that use fixed-format
    // expressions. This is why we use arenas: they speed up allocation and let us use IDs instead
    // of owning pointers during intermediate stages.
    //
    // Note that it's still assumed that each expression is only referred to from one place --
    // there's no CoW, and rewrites may arbitrarily modify expressions under the assumption that
    // this won't affect other statements.
    let mut arena: Arena<'code> = Arena::new();

    // An overarching assumption made by many passes is that all code is reachable. For example,
    // we expect `break` and `continue` to be the last statement in a block. But "reachable" is hard
    // to define rigorously -- is the body of `if (1 == 2)` reachable? -- yet important to define
    // consistently to make sure passes don't make incompatible assumptions.
    //
    // Our definition of reachability is purely syntactic. We treat both `if` branches as reachable
    // and assume all conditions are non-trivial. This includes even `if (1)`, as long as `1`
    // appeared as a constant in bytecode (rather than being inserted implicitly). The `catch` body
    // is always considered reachable, even if the `try` body contains no throwing instructions or
    // is entirely empty. This produces good results as long as compilers don't emit control flow
    // that didn't exist in source.

    // Perhaps the most confusing part among all the logic here is exception handling. Everything
    // else is documented extensively in the source code of the corresponding passes, but EH parsing
    // is spread over many passes because the bytecode doesn't store EH info in an immediately
    // usable format, so we have to convert it and account for it all the time. In a nutshell:
    //
    // 1. During initial IR construction, `try` regions corresponding to the same `try` block are
    //    merged into a single entity.
    // 2. When the stackless IR is built, `catch` bodies are populated with some initializers and
    //    jumps to the handler.
    // 3. `catch` bodies are inlined into handlers, `catch`-alls are rewritten to `finally` blocks,
    //    `finally` is handled, and the format of `try` blocks is finalized in the main EH pass.

    // We delay the construction of a true IR for a bit to reduce the number of (usually slow)
    // recursive rewrites. Everything that can be quickly computed from the bytecode should be done
    // beforehand. This mostly covers control flow analysis and computing stack sizes at each
    // instruction, both of which significantly affect the resulting IR.
    //
    // This pass produces: a list of basic blocks, but without the parsed statements; the CFG, which
    // will become useful when we get to the SSA-related stuff; and the `catch` regions.
    let preparsed_ir = build_preparse_ir(pool, &code, class_info)?;

    // We could topsort the basic blocks to hopefully deobfuscate control flow, but that has
    // a chance to worsen the decompilation output on non-obfuscated code. Any attempts to reorder
    // javac output would produce code further from the source, so we don't do that. If or when
    // control flow obfuscation becomes a problem, we can consider changing this.

    let descriptor = MethodDescriptor::parse(pool.retrieve(method.descriptor())?)?;
    let is_static = method.access_flags().contains(AccessFlags::STATIC);

    // The first actual IR (i.e.: containing statements) that we build is imperative and uses
    // variables instead of JVM's stack. The control flow is unstructured and basic block-based. The
    // number of distinct statement types is greatly reduced because most instructions are
    // translated as `var := expr`.
    let stackless_ir = build_stackless_ir(
        class_info,
        &mut arena,
        pool,
        &code,
        &descriptor,
        is_static,
        preparsed_ir,
    )?;

    // Linearize statements by merging statement lists in basic blocks and dropping BB information.
    let linear_ir = linearize_ir(stackless_ir);

    // The second IR has structured control flow represented via *blocks* -- not to be confused with
    // basic blocks from the CFG world. A block is a syntactic construct that supports jumps to its
    // beginning and end via `continue` and `break`, much like with loops. In all other ways, this
    // IR is as low-level as the stackless one.
    //
    // An important thing to note is how this IR represents exceptions. There is a very basic form
    // of `try`..`catch` blocks for exception handling, though without `finally`. There is no
    // guarantee that every statement within `try` boundaries is actually supposed to be covered by
    // EH: only statements whose indices lie within the `active_ranges` property of the
    // `try`..`catch` block forward exceptions to `catch`.
    let structured_ir = structure_control_flow(&arena, linear_ir);

    // Due to the `active_ranges` gimmick, the behavior of the abstract machine at this point is not
    // local, which means that inlining can change the behavior of the code if statements are
    // inlined across different EH contexts. This forces us to dedicate a separate pass just to
    // handling `try` blocks.
    let eh_ir = parse_try_blocks(&arena, structured_ir);

    // println!("{}", arena.debug(&eh_ir));

    // This pass extends the IR with higher-level constructs and transforms blocks into such.
    // Calling this an optimization pass would be dishonest, since there is no reasoning involved
    // and only trivial inlining is performed, but that's the main idea. This pass also annotates
    // statements with some useful control flow metadata.
    let cf_ir = decompile_cf_constructs(&mut arena, eh_ir);

    // for stmt_meta in &cf_ir {
    //     println!("{}", arena.debug(&stmt_meta));
    // }
    // println!();

    // method attributes: +Code, Exceptions (§4.7.5), Synthetic (§4.7.8), Signature (§4.7.9), Deprecated (§4.7.15), RuntimeVisibleAnnotations (§4.7.16), RuntimeInvisibleAnnotations (§4.7.17), RuntimeVisibleParameterAnnotations (§4.7.18), RuntimeInvisibleParameterAnnotations (§4.7.19), and AnnotationDefault
    // code attributes: LocalVariableTable (§4.7.13), LocalVariableTypeTable (§4.7.14), and +StackMapTable

    Ok(())
}

fn main() {
    // let raw_bytes = include_bytes!("/home/purplesyringa/mc/public/server-1.21.5/avx.class");
    // let raw_bytes = std::fs::read("/home/purplesyringa/mc/public/server-1.21.5/dao.class")
    //     .expect("failed to read class file");
    // let raw_bytes = include_bytes!("/home/purplesyringa/mc/public/vineflower-1.11.1-slim/org/jetbrains/java/decompiler/modules/decompiler/exps/InvocationExprent.class");

    // let raw_bytes =
    //     &*std::fs::read("/home/purplesyringa/mc/public/server-1.21.5/exv$a.class").unwrap();

    // let raw_bytes = &*std::fs::read("Test.class").unwrap();
    // if let Err(e) = decompile_class_file(raw_bytes) {
    //     panic!("class decompilation failed: {e}");
    // }

    let start = Instant::now();
    for entry in std::fs::read_dir("/home/purplesyringa/mc/public/server-1.21.5").expect("files") {
        let entry = entry.expect("files");
        if !entry.path().extension().is_some_and(|ext| ext == "class") {
            continue;
        }
        // println!("file {:?}", entry.path());
        let raw_bytes = std::fs::read(entry.path()).expect("files");
        if let Err(e) = decompile_class_file(&raw_bytes) {
            panic!("class decompilation failed: {e}");
        }
    }
    println!("elapsed {:?}", start.elapsed());

    // let raw_bytes = std::fs::read("Test.class").expect("failed to read class file");

    // if let Err(e) = decompile_class_file(&raw_bytes) {
    //     panic!("class decompilation failed: {e}");
    // }
}
