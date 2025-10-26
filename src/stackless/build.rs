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
// A minor complication arises in exception handlers, which are populated with the exception object
// in `stack0`. The exception is assumed to be stored in the synthetic variable `exception0`; but we
// cannot really insert the statement `stack0 = exception0` anywhere in the IR, because EH BBs can
// be also entered by fallthrough. We thus simulate this statement by storing it in the per-handler
// `struct` and tuning passes to assume it's part of the CFG, as if it runs on the *edge* rather
// than inside nodes. This allows many accesses to `stack0` (as well as copies in other stack
// elements) to be optimized to use `exception0`, but still allows for sound handling of situations
// like:
//     value0 = 1
//     stack0 = value0
//     // exception handler starts here
//     stack1 = stack0
// ...where `stack0` may refer either to the exception or another value depending on control flow.
// The assignment will be inserted into the IR when we generate structured IR in this case.
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
use super::{
    BasicBlock, ExceptionHandler, ExceptionHandlerBlock, InternalBasicBlock, Program, Statement,
};
use crate::ClassInfo;
use crate::ast::{Arena, Expression, Variable, VariableName, VariableNamespace};
use crate::preparse::{self, insn_stack_effect::type_descriptor_width};
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

    let mut ir_basic_blocks = Vec::new();
    // +1 for a fake entry BB populating method arguments. This needs to be done in a separate basic
    // block and not as part of the first real BB, as the first BB may have predecessors.
    ir_basic_blocks.resize_with(preparsed_program.basic_blocks.len() + 1, || {
        InternalBasicBlock {
            sealed_bb: SealedBlock::default(),
            predecessors: Vec::new(),
            eh: None,
        }
    });

    // Initialize method arguments
    let entry_bb_id = preparsed_program.basic_blocks.len();
    machine.bb_id = entry_bb_id;
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
    ir_basic_blocks[entry_bb_id].sealed_bb = machine.seal_basic_block();
    ir_basic_blocks[0].predecessors.push(entry_bb_id);

    // Accumulate `try` ranges for exception handlers.
    let mut eh_entry_for_bb_ranges = vec![Vec::new(); preparsed_program.basic_blocks.len()];
    for handler in &preparsed_program.exception_handlers {
        eh_entry_for_bb_ranges[handler.target].push(handler.active_range.clone());
    }

    // Iterate over BB instruction ranges instead of the whole code, as dead BBs may contain invalid
    // bytecode and we'd rather not worry about that.
    for (bb_id, (bb, eh_entry_for_bb_ranges)) in preparsed_program
        .basic_blocks
        .iter_mut()
        .zip(eh_entry_for_bb_ranges)
        .enumerate()
    {
        machine.stack_size = bb.stack_size_at_start;
        machine.bb_id = bb_id;

        ir_basic_blocks[bb_id].eh = if eh_entry_for_bb_ranges.is_empty() {
            None
        } else {
            Some(ExceptionHandlerBlock {
                eh_entry_for_bb_ranges,
                stack0_def: arena.alloc_with(|version| {
                    Expression::Variable(Variable {
                        name: VariableName {
                            namespace: VariableNamespace::Stack,
                            id: 0,
                        },
                        version,
                    })
                }),
                exception0_use: arena.alloc_with(|version| {
                    Expression::Variable(Variable {
                        name: VariableName {
                            namespace: VariableNamespace::Exception,
                            id: 0,
                        },
                        version,
                    })
                }),
                stack0_exception0_copy_is_necessary: true, // populated by `splitting`
            })
        };

        for succ_bb_id in &bb.successors {
            ir_basic_blocks[*succ_bb_id].predecessors.push(bb_id);
        }

        // Place a label at the beginning of each BB, since we need to resolve addresses in jump
        // targets or `try` blocks to statement indices. We can't read `statements.len()` and
        // populate a map directly here, as statements will be rearranged in a bit by
        // `merge_versions_across_basic_blocks`.
        machine.add(Statement::Label);

        for row in code.raw_instructions_from(Index::new(bb.instruction_range.start))? {
            let (address, insn) = row?;
            let address = address.as_u32();
            if address >= bb.instruction_range.end {
                assert_eq!(address, bb.instruction_range.end);
                break;
            }

            let stack_size_before_insn = machine.stack_size;
            // Jump targets are initialized to instruction addresses. We'll remap them to statement
            // indices after all instructions have been converted. BB-local variable accesses are
            // immediately linked and resolved for splitting, only cross-BB accesses will need to be
            // handled explicitly.
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
    let mut statements = machine.statements;

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
    merge_versions_across_basic_blocks(
        arena,
        &mut ir_basic_blocks,
        &unresolved_uses,
        &mut statements,
    );

    // Fixup jump destinations
    let mut bb_stmt_starts = Vec::new();
    let mut transitions = Vec::new();
    let mut stmt_index = 0;
    statements.retain(|stmt| match stmt {
        Statement::Basic(_) => {
            stmt_index += 1;
            true
        }
        Statement::Label => {
            bb_stmt_starts.push(stmt_index);
            false
        }
        Statement::Jump { .. } | Statement::Switch { .. } => {
            transitions.push(stmt_index);
            stmt_index += 1;
            true
        }
    });
    bb_stmt_starts.push(statements.len());

    let address_to_stmt_index = |address: u32| -> usize {
        let bb_id = preparsed_program
            .basic_blocks
            .binary_search_by_key(&address, |bb| bb.instruction_range.start)
            .expect("invalid jump destination");
        bb_stmt_starts[bb_id]
    };
    for stmt_index in transitions {
        match &mut statements[stmt_index] {
            Statement::Jump { target, .. } => *target = address_to_stmt_index(*target as u32),
            Statement::Switch { arms, default, .. } => {
                for (_, target) in arms {
                    *target = address_to_stmt_index(*target as u32);
                }
                *default = address_to_stmt_index(*default as u32);
            }
            _ => unreachable!(),
        }
    }

    // Compute new exception handlers.
    let mut exception_handlers = Vec::new();
    for handler in preparsed_program.exception_handlers {
        // `start` and `end` may compare equal if all basic blocks covered by the `try` block are
        // e.g. `nop`s. But that's not a good reason to remove the handler. Although we know this
        // means `catch` is never executed, removing the exception handler can cause more code to
        // become *syntactically* unreachable, which violates our assumption that all code in the IR
        // is syntactically reachable. Retaining an empty `try` is better than breaking those
        // assumptions.
        let start = bb_stmt_starts[handler.active_range.start];
        let end = bb_stmt_starts[handler.active_range.end];

        let target = bb_stmt_starts[handler.target];
        let eh = ir_basic_blocks[handler.target].eh.as_ref().unwrap();

        exception_handlers.push(ExceptionHandler {
            stmt_range: start..end,
            bb_range: handler.active_range,
            target_stmt: target,
            class: handler.class,
            // Since multiple handlers can have the same target, these IDs are not unique and can
            // only be used as versions, not as expression IDs.
            stack0_exception0_copy_versions: eh
                .stack0_exception0_copy_is_necessary
                .then_some((eh.stack0_def, eh.exception0_use)),
        });
    }

    // Collect simple BB info for basic stages. We're not interested in the fake entry BB, so remove
    // it.
    ir_basic_blocks.pop();
    ir_basic_blocks[0].predecessors.remove(0);
    let basic_blocks = ir_basic_blocks
        .into_iter()
        .enumerate()
        .map(|(bb_id, bb)| BasicBlock {
            stmt_range: bb_stmt_starts[bb_id]..bb_stmt_starts[bb_id + 1],
            predecessors: bb.predecessors,
        })
        .collect();

    Ok(Program {
        statements,
        basic_blocks,
        exception_handlers,
    })
}
