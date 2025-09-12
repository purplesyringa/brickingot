mod abstract_eval;
mod insn_ir_import;
mod linking;
mod splitting;

use self::abstract_eval::{Machine, SealedBlock};
use self::insn_ir_import::{InsnIrImportError, import_insn_to_ir};
use self::linking::link_stack_across_basic_blocks;
use self::splitting::merge_versions_across_basic_blocks;
use crate::arena::{Arena, DebugIr, ExprId};
use crate::ast::{BasicStatement, Expression, Str, Variable, VariableName, VariableNamespace};
use crate::preparse;
use crate::preparse::insn_stack_effect::is_type_descriptor_double_width;
use core::fmt::{self, Display};
use core::ops::Range;
use noak::{
    MStr,
    descriptor::MethodDescriptor,
    error::DecodeError,
    reader::{
        attributes::{Code, Index},
        cpool::ConstantPool,
    },
};
use rustc_hash::FxHashMap;
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

#[derive(Debug)]
pub struct Program<'code> {
    pub statements: Vec<Statement>,
    pub exception_handlers: Vec<ExceptionHandler<'code>>,
}

impl<'code> DebugIr<'code> for Program<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        for (i, stmt) in self.statements.iter().enumerate() {
            write!(f, "{i}: {}\n", arena.debug(stmt))?;
        }
        for handler in &self.exception_handlers {
            write!(f, "{handler}\n")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum Statement {
    Basic(BasicStatement),
    Label {
        bb_id: usize,
    },
    Jump {
        condition: ExprId,
        target: usize,
    },
    Switch {
        key: ExprId,
        arms: Vec<(i32, usize)>,
        default: usize,
    },
}

impl<'code> DebugIr<'code> for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        match self {
            Self::Basic(stmt) => write!(f, "{}", arena.debug(stmt)),
            Self::Label { bb_id } => write!(f, "bb{bb_id}:"),
            Self::Jump { condition, target } => {
                write!(f, "if ({}) jump {target};", arena.debug(condition))
            }
            Self::Switch { key, arms, default } => {
                write!(f, "switch ({}) ", arena.debug(key))?;
                for (value, target) in arms {
                    write!(f, "{value} => jump {target}; ")?;
                }
                write!(f, "default => jump {default};")
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct ExceptionHandler<'code> {
    pub active_range: Range<usize>,
    pub target: usize,
    pub class: Option<Str<'code>>,
    pub stack0_exception0_copy_versions: Option<(ExprId, ExprId)>,
}

impl Display for ExceptionHandler<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "try {{ {:?} }} catch ({}) {{ goto {}; }}",
            self.active_range,
            self.class
                .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
            self.target,
        )
    }
}

pub struct BasicBlock {
    pub sealed_bb: SealedBlock,
    /// Excludes throwing locations that call into this BB for exception handling.
    pub predecessors: Vec<usize>,
    pub eh: Option<ExceptionHandlerBlock>,
}

pub struct ExceptionHandlerBlock {
    pub eh_entry_for_bb_ranges: Vec<Range<usize>>,
    // stack0 in implicit `stack0 = exception0`.
    pub stack0_def: ExprId,
    // exception0 in implicit `stack0 = exception0`.
    pub exception0_use: ExprId,
    pub stack0_exception0_copy_is_necessary: bool,
}

impl BasicBlock {
    fn new() -> Self {
        Self {
            sealed_bb: SealedBlock::default(),
            predecessors: Vec::new(),
            eh: None,
        }
    }
}

pub fn build_stackless_ir<'code>(
    arena: &mut Arena<'code>,
    pool: &ConstantPool<'code>,
    code: &Code<'code>,
    method_descriptor: &MethodDescriptor<'code>,
    is_static: bool,
    mut preparse_basic_blocks: Vec<preparse::BasicBlock>,
) -> Result<Program<'code>, StacklessIrError> {
    // This IR, and more specifically the nuances of optimizations we apply to it, is a bit weird.
    //
    // We obviously have variables for locals, named `slotN`. We also need to simulate stack and
    // be able to deduce what value each stack element contains across BBs -- so we have variables
    // named `stackN`, denoting the N-th element from the bottom of the stack (category two types
    // occupy two elements, with the entire value stored in the first element).
    //
    // We want to, in a certain sense, inline certain variable definitions, but not others.
    // Specifically, assignments to and reads from locals can be interpreted as side effects, as
    // javac normally only emits them on user request, and not optimizing them gets us closer to
    // source. Operations on stack, however, should obviously be inlineable:
    // `stack0 = <expr>; stack1 = stack0 + 1` should eventually be rewritten to
    // `stack1 = <expr> + 1` if this particular assignment of `stack0` is not seen by any other use.
    //
    // This gets a bit trickier when you realize that we need to "see through" *moves* between
    // stack elements, which commonly arise due to `dup` or `swap` variants, even as the origins of
    // the values are overwritten. For example, in
    //     stack0 = <expr>
    //     stack1 = stack0
    //     stack0 = null
    // ...we want to understand that `stack1` now contains `<expr>`, even though neither
    // `stack1 = stack0` nor `stack0 = <expr>` hold anymore. That requires giving expressions unique
    // IDs, but retrofitting this onto an imperative IR gets ugly because there's now two different
    // kinds of names: expression names and variable names, where variables are also split into two
    // groups -- synthetics, like `stackN`, and locals, like `slotN`, only one of which is subject
    // to inlining.
    //
    // We use a slightly different, unified approach. Each non-trivial expression is assigned to
    // a unique `valueN` variable, which is then copied into a stack variable:
    //     value0 = <expr>
    //     stack0 = value0
    // We can then optimize all uses of `stack0` to `value0`, at least as long as `value0` is not
    // reassigned between the definition of `stack0` and the use, and all visible definitions of
    // `stack0` are equivalent to `stack0 = value0`. For lack of a better word, we call this process
    // "linking". Linking can see through chains of moves and replaces most `stackN` uses with
    // `valueM`.
    //
    // For the purposes of linking, most expressions are considered non-trivial, including literals.
    // The only exception is statements like `stackN = stackM`: in this case, an explicit `valueK`
    // variable will not be created to save `stackM` to if `stackM` already has a known value.
    //
    // Note that linking is only superficially similar to inlining:
    // - Inlining optimizes `x = <expr>; ... x` to `<expr>` when `...` has no side effects; linking
    //   optimizes `x = <var>; ... x` to `<var>` regardless of side effects, because `<var>` is
    //   guaranteed not to have side effects.
    // - Inlining acts on structurized control flow and can handle ternaries and short-circuiting
    //   logic operators; linking applies on the unstructured CFG level and can only link to
    //   a single definition.
    // They achieve different goals with different methods, and so are both necessary. Additionally,
    // linking is more performance-critical, as the unoptimized IR has many synthetic
    // `stackN = stackM` copies.
    //
    // The uses of `stackN` that linking cannot optimize out are precisely the places where SSA
    // would place `phi` functions. Such variables are retained. This can happen in a ternary
    // expression or in a loop, but javac never accesses stack elements populated by the previous
    // loop iteration, so this doesn't need explicit handling in practice.
    //
    // A minor complication arises in exception handlers, which are populated with the expection
    // object in `stack0`. The exception is assumed to be stored in the synthetic variable
    // `exception0`; but we cannot really insert the statement `stack0 = exception0` anywhere in the
    // IR, because EH BBs can be also entered by fallthrough. We thus simulate this statement by
    // storing it in the per-handler `struct` and tuning passes to assume it's part of the CFG. This
    // allows many accesses to `stack0` (as well as copies in other stack elements) to be optimized
    // to use `exception0`, but still allows for sound handling of situations like:
    //     value0 = 1
    //     stack0 = value0
    //     // exception handler starts here
    //     stack1 = stack0
    // ...where `stack0` may refer either to the exception or another value depending on control
    // flow. The assignment will be inserted into the IR when we generate structured IR in this
    // case.
    //
    // On a higher level, linking can be seen as merging certain variables together. However, it's
    // also important to split identical variables apart when they have non-intersecting uses. This
    // includes not just `stackN` variables, but also `slotN` variables, as locals in
    // non-intersecting scopes can be allocated to the same slot. We call this process "splitting".
    //
    // Splitting is implemented by adding unique "versions" to each `slotN`/`stackN` variable
    // mention and merging together versions in use-def chains. This ensures that all definitions
    // that a given use sees, as well as the use itself, access the same variable.
    //
    // In this sense, splitting is actually merging; but don't let that confuse you. Versioning does
    // not create *new* variables from the semantic point of view: different versions of a variable
    // still use the same storage on the IR level, and only reads of the latest version are allowed.
    // This is sound to *implement* by having multiple variables, but passes cannot assume that is
    // the case.
    //
    // Uses from dead stack stores are ignored: `stack0 = value0` does not count as a use of
    // `value0` unless `stack0` is transitively used by something other than a dead stack store.
    //
    // Splitting is performed after linking for two reasons: a) linking has enough to worry about
    // without versions, b) linking turns many stack stores dead, enabling better and faster
    // splitting.
    //
    // Both processes can be performed without SSA, using simpler algorithms with better
    // performance. Both linking and splitting require tracking use-def chains, so we use the same
    // data structures for both tasks.

    let mut machine = Machine::new(arena);

    let mut ir_basic_blocks = Vec::new();
    // +1 for a fake entry BB populating method arguments. This needs to be done in a separate basic
    // block and not as part of the first real BB, as the first BB may have predecessors.
    ir_basic_blocks.resize_with(preparse_basic_blocks.len() + 1, BasicBlock::new);

    // Initialize method arguments
    let entry_bb_id = preparse_basic_blocks.len();
    machine.bb_id = entry_bb_id;
    let mut next_slot_id = 0;
    if !is_static {
        machine.set_slot(next_slot_id, arena.alloc(Expression::This));
        next_slot_id += 1;
    }
    for (index, ty) in method_descriptor.parameters().enumerate() {
        let value = arena.alloc(Expression::Argument { index });
        machine.set_slot(next_slot_id, value);
        next_slot_id += if is_type_descriptor_double_width(&ty) {
            2
        } else {
            1
        };
    }
    ir_basic_blocks[entry_bb_id].sealed_bb = machine.seal_basic_block();
    ir_basic_blocks[0].predecessors.push(entry_bb_id);

    // Iterate over BB instruction ranges instead of the whole code, as dead BBs may contain invalid
    // bytecode and we'd rather not worry about that.
    for (bb_id, bb) in preparse_basic_blocks.iter_mut().enumerate() {
        if bb.instruction_range.end == 0 {
            // Skip empty BBs -- don't let them emit out-of-order labels.
            continue;
        }

        machine.stack_size = bb.stack_size_at_start.get();
        machine.bb_id = bb_id;

        ir_basic_blocks[bb_id].eh = if bb.eh_entry_for_bb_ranges.is_empty() {
            None
        } else {
            Some(ExceptionHandlerBlock {
                eh_entry_for_bb_ranges: core::mem::take(&mut bb.eh_entry_for_bb_ranges),
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
        // populate a map directly here, as statements will be rearranged in a bit.
        machine.add(Statement::Label { bb_id });

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
            import_insn_to_ir(&mut machine, pool, address, &insn).map_err(|error| {
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
    // quadratic piece of the decompiler.
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
    let mut addresses_and_statements = Vec::new();
    let mut transitions = Vec::new();
    let mut stmt_index = 0;
    statements.retain(|stmt| match stmt {
        Statement::Basic(_) => {
            stmt_index += 1;
            true
        }
        Statement::Label { bb_id } => {
            addresses_and_statements.push((
                preparse_basic_blocks[*bb_id].instruction_range.start,
                stmt_index,
            ));
            false
        }
        Statement::Jump { .. } | Statement::Switch { .. } => {
            transitions.push(stmt_index);
            stmt_index += 1;
            true
        }
    });
    let address_to_stmt_index = |address: usize| {
        let index = addresses_and_statements
            .binary_search_by_key(&address, |(other_address, _)| *other_address as usize)
            .expect("invalid jump destination");
        addresses_and_statements[index].1
    };
    for stmt_index in transitions {
        match &mut statements[stmt_index] {
            Statement::Jump { target, .. } => *target = address_to_stmt_index(*target),
            Statement::Switch { arms, default, .. } => {
                for (_, target) in arms {
                    *target = address_to_stmt_index(*target);
                }
                *default = address_to_stmt_index(*default);
            }
            _ => unreachable!(),
        }
    }

    // Compute new exception handlers.
    let mut handler_to_copy = FxHashMap::default();
    for (prepare_bb, ir_bb) in preparse_basic_blocks.iter().zip(&ir_basic_blocks) {
        if let Some(eh) = &ir_bb.eh
            && eh.stack0_exception0_copy_is_necessary
        {
            handler_to_copy.insert(
                prepare_bb.instruction_range.start,
                (eh.stack0_def, eh.exception0_use),
            );
        }
    }

    let mut exception_handlers = Vec::new();
    for handler in code.exception_handlers() {
        // Since some instructions could have been optimized out as unreachable, `start_pc` and
        // `stop_pc` don't necessarily correspond to any existing basic block boundary! Look for the
        // region of present basic blocks that fit within the range.

        let start_pos = addresses_and_statements
            .partition_point(|(address, _)| *address < handler.start().as_u32());
        let end_pos = addresses_and_statements
            .partition_point(|(address, _)| *address < handler.end().as_u32());
        if start_pos == addresses_and_statements.len() || end_pos <= start_pos {
            continue;
        }

        // `start_index` and `end_index` may compare equal, which indicates that the `try` body is
        // empty, but that's not a good reason to remove the handler. Although we know this means
        // `catch` is never executed, removing the exception handler can cause more code to become
        // *syntactically* unreachable, which violates our assumption that all code in the IR is
        // syntactically reachable.
        let start_index = addresses_and_statements[start_pos].1;
        let end_index = if end_pos == addresses_and_statements.len() {
            statements.len()
        } else {
            addresses_and_statements[end_pos].1
        };

        exception_handlers.push(ExceptionHandler {
            active_range: start_index..end_index,
            target: address_to_stmt_index(handler.handler().as_u32() as usize),
            class: match handler.catch_type() {
                Some(catch_type) => Some(Str(pool.retrieve(catch_type)?.name)),
                None => None,
            },
            // Since multiple handlers can have the same target, these IDs are not unique and can
            // only be used as versions, not as expression IDs.
            stack0_exception0_copy_versions: handler_to_copy
                .get(&handler.handler().as_u32())
                .copied(),
        });
    }

    Ok(Program {
        statements,
        exception_handlers,
    })
}
