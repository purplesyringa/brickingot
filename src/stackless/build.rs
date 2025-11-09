// This IR, and more specifically the nuances of optimizations we apply to it, is a bit weird.
//
// Disclaimer: this is not an SSA form, but it's close to it in motivation, and some algorithms
// should remind you of the ones you might see in SSA construction. While SSA is easy to *use* in
// compilers, building and then compiling it back into imperative code is non-trivial and would be
// more complex than the passes we'd want to run on the SSA itself. We can achieve basically
// everything we need with more control and better performance if we skip SSA. The only benefit of
// using SSA would be familiarity, and I have to admit I'm not sufficiently familiar with efficient
// SSA construction to take this risk. Disclaimer over.
//
// We obviously have variables for locals, named `slotN`. We also need to simulate stack and be able
// to deduce what value each stack element contains across BBs -- so we have variables named
// `stackN`, denoting the N-th element from the bottom of the stack (category two types occupy two
// elements, with the entire value stored in the first element).
//
// We want to, in a certain sense, inline certain variable definitions, but not others.
// Specifically, assignments to and reads from locals can be interpreted as side effects, as javac
// normally only emits them on user request, and not optimizing them gets us closer to source.
// Operations on stack, however, should obviously be inlineable:
// `stack0 = <expr>; stack1 = stack0 + 1` should eventually be rewritten to `stack1 = <expr> + 1` if
// this particular assignment to `stack0` is not seen by any other use.
//
// This gets a bit trickier when you realize that we need to "see through" *moves* between stack
// elements, which commonly arise due to `dup` or `swap` variants, even as the origins of the values
// are overwritten. For example, in
//     stack0 = <expr>
//     stack1 = stack0
//     stack0 = null
// ...we want to understand that `stack1` now contains `<expr>`, even though neither
// `stack1 = stack0` nor `stack0 = <expr>` hold anymore. That requires giving expressions unique
// IDs, but retrofitting this onto an imperative IR gets ugly, since there's be two kinds of IDs:
// expression IDs and variable names.
//
// We use a unified approach instead. Each non-trivial expression is first assigned to a unique
// `valueN` variable, which effectively acts as an expression ID. This variable is then copied to
// a synthetic stack variable:
//     value0 = <expr>
//     stack0 = value0
// This means that all we need to track is which stack variables were assigned from which value
// variables (transitively). In this example, we can optimize all uses of `stack0` to `value0` as
// long as `value0` is not reassigned between the definition of `stack0` and the use, and all
// visible definitions of `stack0` are equivalent to `stack0 = value0`. For lack of a better word,
// we call this process "linking". Linking can see through chains of moves and replaces most
// `stackN` uses with `valueM`.
//
// For the purposes of linking, most expressions are considered non-trivial, including literals. The
// only exception is statements like `stackN = stackM`: in this case, an explicit `valueK` variable
// will not be created to save `stackM` to if `stackM` is already linked to a known value variable.
//
// Note that linking (stack variables to values) is only superficially similar to inlining
// (expressions into other expressions):
// - Inlining optimizes `x = <expr>; ... x` to `<expr>` when `...` has no side effects, whereas
//   linking optimizes `x = <var>; ... x` to `<var>` regardless of side effects, because `<var>` is
//   guaranteed not to have side effects.
// - Inlining acts on structurized control flow and can handle ternaries and short-circuiting logic
//   operators; linking applies on the unstructured CFG level and can only link to a single
//   definition.
// They achieve different goals with different methods, and so are both necessary. Additionally,
// linking is more performance-critical, as the unoptimized IR has many synthetic `stackN = stackM`
// copies. We won't cover inlining here.
//
// The uses of `stackN` that linking cannot optimize out are precisely the places where SSA would
// place `phi` functions. Such variables are retained. This can happen in a ternary expression or in
// a loop, but javac never accesses stack elements populated by the previous loop iteration, so this
// doesn't need explicit handling in practice.
//
// A minor complication arises in exception handlers. Each `catch` statement is associated with
// a `valueN` variable implicitly populated with the exception object when an exception is caught.
// After this, `stack0 = valueN` should be executed; but we cannot insert this statement into the
// IR at any location, since EH BBs can be also entered by fallthrough. We thus simulate this
// statement by storing it in the per-handler `struct` and tuning passes to assume it's part of the
// CFG, as if it runs on the *edge* rather than inside nodes. This enables correct handling of code
// like:
//     value0 = 1
//     stack0 = value0
//     // exception handler starts here
//     stack1 = stack0
// ...where `stack0` may refer either to the exception or another value depending on control flow.
// In this case, the assignment `stack0 = valueN` is necessary, and will be inserted into the
// structured IR later.
//
// On a higher level, linking can be seen as merging certain variables together. However, it's also
// important to split identically named variables apart when they have non-intersecting uses. This
// includes not just `stackN` variables, but also `slotN` variables, as locals in non-intersecting
// scopes can be allocated to the same slot. We call this process "splitting".
//
// Splitting is implemented by adding unique "versions" to each `slotN`/`stackN` variable mention
// and merging together versions in use-def chains. This ensures that all definitions that a given
// use sees, as well as the use itself, access the same variable.
//
// In this sense, splitting is actually merging; but don't let that confuse you. Versioning does not
// create *new* variables from the semantic point of view: different versions of a variable are
// still allowed to use the same storage in the abstract machine, i.e. only reads from the latest
// version are allowed. This is sound to *implement* by having multiple variables, but passes cannot
// assume that is the case.
//
// Uses from dead stack stores are ignored: `stack0 = value0` does not count as a use of `value0`
// unless `stack0` is transitively used by something other than a dead stack store.
//
// Splitting is performed after linking for two reasons: a) linking has enough to worry about
// without versions, b) linking turns many stack stores dead, enabling better and faster splitting.
//
// Both processes can be performed without SSA, using simpler algorithms with better performance.
// Both linking and splitting require tracking use-def chains, so we use the same data structures
// for both tasks.

use super::abstract_eval::{Machine, SealedBlock};
use super::insn_ir_import::{InsnIrImportError, import_insn_to_ir};
use super::linking::link_stack_across_basic_blocks;
use super::splitting::merge_versions_across_basic_blocks;
use super::{BasicBlock, CatchHandler, ExceptionHandlerBlock, InternalBasicBlock, Program};
use crate::ClassInfo;
use crate::ast::{Arena, BasicStatement, Expression};
use crate::preparse::{self, insn_stack_effect::type_descriptor_width};
use crate::var;
use noak::{
    descriptor::MethodDescriptor,
    error::DecodeError,
    reader::{
        attributes::{Code, Index},
        cpool::ConstantPool,
    },
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum StacklessIrError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error(
        "While importing instruction `{address}: {insn}` to IR: {error} (stack size before instruction was {stack_size_before_insn})"
    )]
    InsnIrImport {
        address: u32,
        insn: String,
        stack_size_before_insn: usize,
        error: InsnIrImportError,
    },
}

pub fn build_stackless_ir<'code>(
    class_info: &mut ClassInfo<'code>,
    arena: &mut Arena<'code>,
    pool: &ConstantPool<'code>,
    code: &Code<'code>,
    method_descriptor: &MethodDescriptor<'code>,
    is_static: bool,
    mut preparsed_program: preparse::Program<'code>,
) -> Result<Program<'code>, StacklessIrError> {
    let mut machine = Machine::new(arena);

    // Add a synthetic BB at the very beginning to populate method arguments and synthetics. This
    // needs to be done in a separate basic block and not as part of the first real BB, as the first
    // BB may have predecessors, which makes everything confusing. Since our BBs are sorted by
    // program order, this shifts all BB IDs by one.
    for bb in &mut preparsed_program.basic_blocks {
        for succ_bb_id in &mut bb.successors {
            *succ_bb_id += 1;
        }
    }
    for handler in &mut preparsed_program.catch_handlers {
        for range in &mut handler.active_ranges {
            range.start += 1;
            range.end += 1;
        }
        handler.target += 1;
    }
    preparsed_program.basic_blocks.insert(
        0,
        preparse::BasicBlock {
            instruction_range: 0..0,
            n_instructions: 0,
            stack_size_at_start: 0,
            successors: vec![1],
        },
    );

    machine.address_to_bb_id = preparsed_program
        .basic_blocks
        .iter()
        .enumerate()
        .map(|(bb_id, bb)| (bb.instruction_range.start, bb_id))
        .collect();

    let mut ir_basic_blocks: Vec<InternalBasicBlock> = (0..preparsed_program.basic_blocks.len())
        .map(|_| InternalBasicBlock {
            sealed_bb: SealedBlock::default(),
            predecessors: Vec::new(),
            eh: None,
        })
        .collect();

    // Initialize method arguments
    machine.bb_id = 0;
    let mut next_slot_id = 0;
    if !is_static {
        machine.set_slot(next_slot_id, arena.alloc(Expression::This));
        next_slot_id += 1;
    }
    for (index, ty) in method_descriptor.parameters().enumerate() {
        let value = arena.alloc(Expression::Argument { index });
        machine.set_slot(next_slot_id, value);
        next_slot_id += type_descriptor_width(ty);
    }
    ir_basic_blocks[0].sealed_bb = machine.seal_basic_block();
    ir_basic_blocks[1].predecessors.push(0);

    // Accumulate information for exception-handling basic blocks. Also generate expressions for
    // implicit `valueN` variable definitions in `catch` statements.
    let mut handler_value_vars = Vec::with_capacity(preparsed_program.catch_handlers.len());
    for handler in &preparsed_program.catch_handlers {
        let value_var = arena.var_name(var!(value machine.next_value_id)).0;
        machine.next_value_id += 1;
        handler_value_vars.push(value_var);

        let eh = match &mut ir_basic_blocks[handler.target].eh {
            Some(eh) => {
                eh.value_var = None;
                eh
            }
            eh @ None => {
                eh.insert(ExceptionHandlerBlock {
                    eh_entry_for_bb_ranges: Vec::new(),
                    // It doesn't make sense to allocate a variable here, since a single target address
                    // may be used by multiple `catch` blocks (e.g. with different classes), so we'd
                    // have to create new allocations.
                    stack_version: arena.version(),
                    value_var: Some(value_var),
                    stack_value_copy_is_necessary: true, // populated by `splitting`
                })
            }
        };
        eh.eh_entry_for_bb_ranges
            .extend(handler.active_ranges.iter().cloned());
    }

    // Iterate over BB instruction ranges instead of the whole code, as dead BBs may contain invalid
    // bytecode and we'd rather not worry about that.
    for (bb_id, preparsed_bb) in preparsed_program
        .basic_blocks
        .iter_mut()
        .enumerate()
        // skip entry BB
        .skip(1)
    {
        machine.stack_size = preparsed_bb.stack_size_at_start;
        machine.bb_id = bb_id;

        for succ_bb_id in &preparsed_bb.successors {
            ir_basic_blocks[*succ_bb_id].predecessors.push(bb_id);
        }

        // Most bytecode instructions correspond to one statement, so this is a good estimate.
        machine.statements.reserve(preparsed_bb.n_instructions + 4);

        for row in code.raw_instructions_from(Index::new(preparsed_bb.instruction_range.start))? {
            let (address, insn) = row?;
            let address = address.as_u32();
            if address >= preparsed_bb.instruction_range.end {
                assert_eq!(address, preparsed_bb.instruction_range.end);
                break;
            }

            let stack_size_before_insn = machine.stack_size;
            // BB-local variable accesses are immediately linked and resolved for splitting, only
            // cross-BB accesses will need to be handled explicitly.
            import_insn_to_ir(class_info, &mut machine, pool, address, &insn).map_err(|error| {
                StacklessIrError::InsnIrImport {
                    address,
                    insn: format!("{insn:?}"),
                    stack_size_before_insn,
                    error,
                }
            })?;
        }

        ir_basic_blocks[bb_id].sealed_bb = machine.seal_basic_block();
    }

    let mut unresolved_uses = machine.unresolved_uses;

    // The core of these algorithms is DFS over nodes `(bb_id, var)`, which denotes that we're
    // interested in finding definitions of `var` visible at the entry to `bb_id`, and edges
    // represent that information needs to be integrated from another node. This makes it the only
    // quadratic part of the decompiler.
    //
    // In practice, the performance is better than what you'd expect from such worst-case time
    // complexity for reasons described in the comments of individual modules.
    //
    // Still, it begs the question: why are there non-linear algorithms at all? The answer is
    // irreducible control flow: we want to track use-def chains in complex CFGs to produce readable
    // output. Of course, realistic programs typically have reducible control flow, but realistic
    // programs are also well-formed enough that the performance of these passes is quite good, so
    // it doesn't make much sense to provide a separate quasilinear implementation.
    link_stack_across_basic_blocks(arena, &ir_basic_blocks, &mut unresolved_uses);
    merge_versions_across_basic_blocks(arena, &mut ir_basic_blocks, &unresolved_uses);

    // Convert `catch` blocks and add `stack0 = valueN` to the body if necessary.
    let catch_handlers = preparsed_program
        .catch_handlers
        .into_iter()
        .zip(handler_value_vars)
        .map(|(handler, value_var)| {
            let eh = ir_basic_blocks[handler.target].eh.as_ref().unwrap();

            let stack_value_copy = eh.stack_value_copy_is_necessary.then(|| {
                BasicStatement::Assign {
                    // Since multiple handlers can have the same target, these IDs are not unique
                    // and can only be used as versions, not as expression IDs.
                    target: arena.var(var!(stack0 v eh.stack_version)),
                    value: arena.var(value_var),
                }
            });

            CatchHandler {
                active_ranges: handler.active_ranges,
                class: handler.class,
                value_var,
                stack_value_copy,
                jump_target: handler.target,
            }
        })
        .collect();

    // Extract BB into a public API for the upcoming stages.
    let basic_blocks = ir_basic_blocks
        .into_iter()
        .map(|bb| BasicBlock {
            statements: bb.sealed_bb.statements,
            predecessors: bb.predecessors,
        })
        .collect();

    Ok(Program {
        basic_blocks,
        catch_handlers,
    })
}
