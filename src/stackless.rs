use crate::abstract_eval::{ActiveDef, Machine};
use crate::arena::{Arena, DebugIr, ExprId};
use crate::ast::{BasicStatement, Expression, Str, VariableName};
use crate::insn_ir_import::{import_insn_to_ir, InsnIrImportError};
use crate::insn_stack_effect::is_type_descriptor_double_width;
use crate::linking::link_stack_across_basic_blocks;
use crate::preparse;
use crate::splitting::merge_versions_across_basic_blocks;
use core::fmt::{self, Display};
use noak::{
    descriptor::MethodDescriptor,
    error::DecodeError,
    reader::{
        attributes::{Code, Index},
        cpool::ConstantPool,
    },
    MStr,
};
use rustc_hash::FxHashMap;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum StacklessIrError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("While importing instruction `{address}: {insn}` to IR: {error} (stack size before instruction was {stack_size_before_insn})")]
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
        address: u32,
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
            Self::Label { address } => write!(f, "I{address}:"),
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

#[derive(Debug)]
pub struct ExceptionHandler<'code> {
    pub start: usize,
    pub end: usize,
    pub target: usize,
    pub class: Option<Str<'code>>,
}

impl Display for ExceptionHandler<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "try {{ {}..{} }} catch ({}) {{ goto {}; }}",
            self.start,
            self.end,
            self.class
                .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
            self.target,
        )
    }
}

pub struct BasicBlock {
    pub active_defs_at_end: FxHashMap<VariableName, ActiveDef>,
    pub predecessors: Vec<usize>,
    pub unique_exception_expr_id: Option<ExprId>,
}

impl BasicBlock {
    fn new() -> Self {
        Self {
            active_defs_at_end: FxHashMap::default(),
            predecessors: Vec::new(),
            unique_exception_expr_id: None,
        }
    }
}

pub fn build_stackless_ir<'code>(
    arena: &mut Arena<'code>,
    pool: &ConstantPool<'code>,
    code: &Code<'code>,
    method_descriptor: &MethodDescriptor<'code>,
    is_static: bool,
    preparse_basic_blocks: Vec<preparse::BasicBlock>,
) -> Result<Program<'code>, StacklessIrError> {
    // This IR, and more specifically the nuances of optimizations we apply to it, is a bit weird.
    //
    // We obviously have variables for locals, named `slotN`. We also need to simulate stack and
    // be able to deduce what value each stack element contains across BBs -- so we have variables
    // named `stackN`, denoting the N-th element from the bottom of the stack (category two types
    // are counted as two elements).
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
    // We use a slightly different, unified approach. Each non-trivial expresison is assigned to
    // a unique `valueN` variable, which is then copied into a stack variable:
    //     value0 = <expr>
    //     stack0 = value0
    // We can then optimize all uses of `stack0` to `value0`, at least as long as `value0` is not
    // reassigned between the definition of `stack0` and the use, and all visible definitions of
    // `stack0` are equivalent to `stack0 = value0`. For lack of a better word, we call this process
    // "linking". Linking can see through chains of moves and replaces most `stackN` uses with
    // `valueM`.
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
    // would place `phi` functions. Such variables are retained.
    //
    // It's worth noting that there's an exception to the rule that `stackN` is always either
    // optimized to `valueM`, or is retained as-is. In exception handlers, `stackN` can also be
    // optimized to `exception0`. Note that such a replacement is not guaranteed, i.e. further
    // passes cannot assume that exceptions aren't referred to directly via `stack0`.
    //
    // On a higher level, linking can be seen as merging certain variables together. However, it's
    // also important to split identical variables apart when they have non-intersecting uses. This
    // includes not just `stackN` variables, but also `slotN` variables, as locals in
    // non-intersecting scopes can be allocated to the same slot. We call this process "splitting".
    //
    // Splitting is implemented by adding "versions" to each `slotN`/`stackN` variable mention and
    // merging together versions in use-def chains. This ensures that all definitions that a given
    // use sees, as well as the use itself, access the same variable. Uses from dead stack stores
    // are ignored: `stack0 = value0` do not count as a use of `value0` unless `stack0` is
    // transitively used by something other than a dead stack store.
    //
    // Splitting is performed after linking for two reasons: a) linking has enough to worry about
    // without versions, b) linking turns many stack stores dead, enabling better and faster
    // splitting.
    //
    // Both of these processes can be performed without SSA, using simpler algorithms with better
    // performance. Both linking and splitting require tracking use-def chains, so we use the same
    // data structures for both tasks.

    let mut machine = Machine::new(arena);

    let mut ir_basic_blocks = Vec::new();
    ir_basic_blocks.resize_with(preparse_basic_blocks.len() + 1, BasicBlock::new);

    // Initialize method arguments. This needs to be done in a separate basic block and not as part
    // of the first BB, as the first BB may have predecessors.
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
    ir_basic_blocks[entry_bb_id].active_defs_at_end = machine.seal_basic_block();
    ir_basic_blocks[0].predecessors.push(entry_bb_id);

    // Iterate over BB instruction ranges instead of the whole code, as dead BBs may contain invalid
    // bytecode and we'd rather not worry about that.
    for (bb_id, bb) in preparse_basic_blocks.iter().enumerate() {
        machine.stack_size = bb.stack_size_at_start;
        machine.bb_id = bb_id;

        ir_basic_blocks[bb_id].unique_exception_expr_id = if bb.eh_entry_for_ranges.is_empty() {
            None
        } else {
            Some(arena.alloc(Expression::Null))
        };
        for succ_bb_id in &bb.successors {
            ir_basic_blocks[*succ_bb_id].predecessors.push(bb_id);
        }

        for row in code.raw_instructions_from(Index::new(bb.instruction_range.start))? {
            let (address, insn) = row?;
            let address = address.as_u32();
            if address >= bb.instruction_range.end {
                assert_eq!(address, bb.instruction_range.end);
                break;
            }

            // XXX: We could only add labels at the exact places we need to resolve, but this
            // doesn't seem to reduce performance too much.
            machine.add(Statement::Label { address });

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

        ir_basic_blocks[bb_id].active_defs_at_end = machine.seal_basic_block();
    }

    let unresolved_uses = machine.unresolved_uses;
    let mut statements = machine.statements;

    link_stack_across_basic_blocks(arena, &ir_basic_blocks, &unresolved_uses);
    merge_versions_across_basic_blocks(arena, &ir_basic_blocks, &unresolved_uses, &mut statements);

    // Fixup jump destinations
    let mut addresses_and_statements = Vec::new();
    let mut transitions = Vec::new();
    let mut stmt_index = 0;
    statements.retain(|stmt| match stmt {
        Statement::Basic(_) => {
            stmt_index += 1;
            true
        }
        Statement::Label { address } => {
            addresses_and_statements.push((*address, stmt_index));
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

    // // Compute new exception handlers
    let mut exception_handlers = Vec::new();
    for handler in code.exception_handlers() {
        // Look for the region of statements that fit within the range, as some instructions could
        // have been optimized out as unreachable.
        let start_index = addresses_and_statements
            .partition_point(|(address, _)| *address < handler.start().as_u32());
        if start_index == addresses_and_statements.len() {
            continue;
        }
        let start = addresses_and_statements[start_index].1;

        let end_index = addresses_and_statements
            .partition_point(|(address, _)| *address <= handler.end().as_u32())
            - 1;
        let end = addresses_and_statements[end_index].1;
        if end <= start {
            continue;
        }

        let target = address_to_stmt_index(handler.handler().as_u32() as usize);

        let class = match handler.catch_type() {
            Some(catch_type) => Some(Str(pool.retrieve(catch_type)?.name)),
            None => None,
        };
        exception_handlers.push(ExceptionHandler {
            start,
            end,
            target,
            class,
        });
    }

    Ok(Program {
        statements,
        exception_handlers,
    })
}
