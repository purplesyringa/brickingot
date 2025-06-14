#![cfg_attr(false, no_std)]

extern crate alloc;

mod arena;
mod arrows;
mod ast;
mod linking;
mod stackless;
// mod cfg;
mod abstract_eval;
mod insn_control_flow;
mod insn_ir_import;
mod insn_stack_effect;
// mod matcher;
// mod unstructured;
mod preparse;

use crate::arena::Arena;
use crate::preparse::{extract_basic_blocks, BytecodePreparsingError};
use crate::stackless::{build_stackless_ir, StacklessIrError};
// use crate::cfg::structurize_cfg;
// use crate::matcher::rewrite_control_flow;
// use crate::unstructured::{convert_code_to_stackless, StatementGenerationError};
use noak::{
    descriptor::MethodDescriptor,
    error::DecodeError,
    reader::{attributes::Code, cpool::ConstantPool, Class, Method},
    AccessFlags, MStr,
};
use std::time::Instant;
use thiserror::Error;

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
    // #[error("While generating initial statements: {0}")]
    // StatementGeneration(#[from] StatementGenerationError),
}

fn decompile_class_file(raw_bytes: &[u8]) -> Result<(), ClassDecompileError> {
    let class = Class::new(&raw_bytes)?;
    let pool = class.pool();

    // let bootstrap_methods: Vec<BootstrapMethod> = match class
    //     .attributes()
    //     .find_attribute::<BootstrapMethods>(pool)?
    // {
    //     Some(methods) => methods.methods().iter().collect::<Result<_, _>>()?,
    //     None => Vec::new(),
    // };

    // TODO: issue a diagnostic if ACC_SUPER is unset

    for method in class.methods() {
        let method = method?;
        decompile_method(pool, &method).map_err(|error| ClassDecompileError::Method {
            name: pool
                .retrieve(method.name())
                .unwrap_or(MStr::from_mutf8(b"??").unwrap())
                .display()
                .to_string(),
            error,
        })?;
    }

    Ok(())
}

fn decompile_method<'code>(
    pool: &ConstantPool<'code>,
    method: &Method<'code>,
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
    // This makes translation between IRs free of boilerplate, but we have to pay for allocation to
    // support expression nesting on each stage, even for IRs that use fixed-format expressions.
    // This is why we use arenas: they speed up allocation and let us use IDs instead of owning
    // pointers during intermediate stages.
    //
    // Note that it's still assumed that each expression is only referred to from one place --
    // there's no CoW, and rewrites may arbitrarily modify expressions under the assumption that
    // this won't affect other statements.
    let mut arena: Arena<'code> = Arena::new();

    // We delay IR construction for a bit to reduce the number of (usually slow) recursive rewrites.
    // Everything that can be quickly computed from the bytecode should be done beforehand. This
    // mostly covers control flow analysis and computing stack sizes at each instruction, both of
    // which significantly affect the IR. We also obtain the CFG as a byproduct, which will become
    // useful when we get to the SSA-related stuff.
    let basic_blocks = extract_basic_blocks(pool, &code)?;

    // We could topsort the basic blocks to hopefully deobfuscate control flow, but that has
    // a chance to worsen the decompilation output on non-obfuscated code. Any attempts to reorder
    // javac output would produce code further from the source, so we don't do that. If or when
    // control flow obfuscation becomes a problem, we can consider changing this.

    let descriptor = MethodDescriptor::parse(pool.retrieve(method.descriptor())?)?;
    let is_static = method.access_flags().contains(AccessFlags::STATIC);

    // The first IR we build is imperative and uses variables instead of JVM's stack. The control
    // flow is unstructured. The number of distinct statement types is greatly reduced because most
    // instructions are translated as `var := expr`. Information about basic blocks is provided
    // separately, but is not an intrinsic part of the IR.
    let stackless_ir = build_stackless_ir(
        &mut arena,
        pool,
        &code,
        &descriptor,
        is_static,
        basic_blocks,
    )?;

    // let unstructured_program = convert_code_to_stackless(arena, pool, &code)?;
    // let mut stmts = structurize_cfg(unstructured_program);
    // rewrite_control_flow(&mut stmts);

    // for stmt in &stackless_ir.statements {
    //     println!("{}", arena.debug(stmt));
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
    // // let raw_bytes = &*std::fs::read("Test.class").unwrap();
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
