pub mod insn_control_flow;
pub mod insn_stack_effect;

use self::insn_control_flow::{InsnControlFlow, get_insn_control_flow};
use self::insn_stack_effect::{InsnStackEffectError, get_insn_stack_effect};
use crate::ast::Str;
use crate::interval_tree::IntervalTree;
use core::cell::Cell;
use core::ops::Range;
use noak::{
    error::DecodeError,
    reader::{
        attributes::{Code, Index},
        cpool::ConstantPool,
    },
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum BytecodePreparsingError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("While analyzing instruction stack effect: {0}")]
    InsnStackEffect(#[from] InsnStackEffectError),

    #[error("Jump address overflows u16")]
    CodeOffsetOutOfBounds,

    #[error("Found execution paths that reach a single address at different stack heights")]
    InconsistentStackSize,

    #[error("Jump or exception handler refers to the middle of an instruction")]
    SplitInstruction,

    #[error("Execution reaches the end of bytecode")]
    CodeFallthrough,

    #[error("Stack underflow")]
    StackUnderflow,
}

#[derive(Debug)]
pub struct BasicBlock {
    /// The range of bytecode instructions covered by this BB, indexed by bytes (rather than
    /// instruction numbers).
    pub instruction_range: Range<u32>,
    /// The size of the stack on entry to this BB, counting double-width elements (`long` and
    /// `double`) as two. The `Cell` is an implementation detail only.
    pub stack_size_at_start: Cell<usize>,
    /// The IDs of BBs the last instruction in this BB can jump to. This includes fallthrough, but
    /// excludes jumps to exception handlers.
    pub successors: Vec<usize>,
}

pub struct Program<'code> {
    pub basic_blocks: Vec<BasicBlock>,
    pub exception_handlers: Vec<ExceptionHandler<'code>>,
}

pub struct ExceptionHandler<'code> {
    pub active_range: Range<usize>,
    pub target: usize,
    pub class: Option<Str<'code>>,
    pub is_reachable: bool,
}

pub fn extract_basic_blocks<'code>(
    cpool: &ConstantPool<'code>,
    code: &Code<'code>,
) -> Result<Program<'code>, BytecodePreparsingError> {
    // Insert splits after every explicit jump, at each jump target, at each exception handler, and
    // at `try` boundaries. Also at the end and the beginning for implementation simplicity. Save
    // all non-trivial transitions to build the CFG without reparsing the instructions.
    let mut should_insert_split_here = false;
    let mut splits = vec![0, code.byte_len()];
    let mut transitions: Vec<(u32, InsnControlFlow)> = Vec::new();

    for row in code.raw_instructions() {
        let (address, insn) = row?;
        let address = address.as_u32();

        if should_insert_split_here {
            splits.push(address);
            should_insert_split_here = false;
        }

        let control_flow = get_insn_control_flow(address, &insn)
            .map_err(|_| BytecodePreparsingError::CodeOffsetOutOfBounds)?;
        splits.extend(&control_flow.can_jump_to);
        if !control_flow.is_normal() {
            transitions.push((address, control_flow));
            should_insert_split_here = true;
        }
    }

    // `should_insert_split_here` can be ignored, as there's an implicit split at the end.

    // Splitting BBs at `try` block enters and exits is not necessary from the CFG point of view,
    // but it simplifies address/statement index tracking during IR construction. It is not spelled
    // entirely clearly in the specification, but it seems like valid JVM bytecode never has
    // `start_pc`/`end_pc` point into the middle of instructions, and HotSpot also verifies that's
    // the case, so we're in good company.
    splits.extend(code.exception_handlers().flat_map(|handler| {
        [
            handler.start().as_u32(),
            handler.end().as_u32(),
            handler.handler().as_u32(),
        ]
    }));

    splits.sort();
    splits.dedup();

    if *splits.last().unwrap() > code.byte_len() {
        return Err(BytecodePreparsingError::CodeOffsetOutOfBounds);
    }

    // For malformed bytecode, splits can be in the middle of instructions. We'll have verified the
    // correctness by the end of this function during DFS.
    let mut basic_blocks: Vec<BasicBlock> = splits
        .windows(2)
        .enumerate()
        .map(|(bb_id, range)| BasicBlock {
            instruction_range: range[0]..range[1],
            stack_size_at_start: Cell::new(0),
            // `successors` can only be populated after BB boundaries have been decided, so this
            // stays in a sentinel-like state where only the trivial successor is recorded. We'll
            // remove it for divergent control flow a bit later.
            successors: vec![bb_id + 1],
        })
        .collect();

    // Fill BB successors
    let mut bb_id = 0;
    for (address, control_flow) in transitions {
        while address >= basic_blocks[bb_id].instruction_range.end {
            bb_id += 1;
        }

        if !control_flow.can_fallthrough {
            // There can be at most one jump origin per BB, so this BB is in a pristine state, and
            // this `clear` call only removes the jump to the next BB.
            basic_blocks[bb_id].successors.clear();
        }

        for target_address in control_flow.can_jump_to {
            // We could use a hashmap here, but that would require us to populate it for each
            // instruction rather than just BB boundaries, so binary search is probably better.
            let target_bb_id = basic_blocks
                .binary_search_by_key(&target_address, |bb| bb.instruction_range.start)
                .expect("jump not to BB start");
            basic_blocks[bb_id].successors.push(target_bb_id);
        }

        let successors = &mut basic_blocks[bb_id].successors;
        successors.sort();
        successors.dedup();
    }

    // *Typically*, the last BB cannot fallthrough, i.e. jump to the non-existent BB after it. We
    // could just emit the error immediately if it does, but then we would emit a false positive if
    // the last BB is actually unreachable. Delay this decision until DFS.

    // Populate exception handling ranges.
    let mut exception_handlers = Vec::new();
    for handler in code.exception_handlers() {
        let [start_bb_id, end_bb_id, handler_bb_id] =
            [handler.start(), handler.end(), handler.handler()].map(|offset| {
                basic_blocks
                    .binary_search_by_key(&offset.as_u32(), |bb| bb.instruction_range.start)
                    .expect("EH not aligned to BB")
            });

        exception_handlers.push(ExceptionHandler {
            active_range: start_bb_id..end_bb_id,
            target: handler_bb_id,
            class: match handler.catch_type() {
                Some(catch_type) => Some(Str(cpool.retrieve(catch_type)?.name)),
                None => None,
            },
            is_reachable: false,
        });
    }

    // Let's talk about the elephant in the room: we aren't using `StackMapTable`. We want to parse
    // pre-Java 6 classfiles (even though we might fail to handle `jsr`), and so we need to support
    // verification by type inference. But overall, it's simply unnecessary: type inference can be
    // performed in linear time if we don't care about object types (and we don't, at least at this
    // moment), and calculating stack sizes is trivial given the infrastructure we have.
    // Additionally, using `StackMapTable` would mean either trusting it, potentially causing
    // accidental panics if it doesn't agree with the bytecode, or verifying it, which would require
    // quite a bit of code; and we'd rather parse than validate.
    //
    // This is a good time to talk about reachability. Verification by type checking requires *all*
    // code to be correctly typed, while verification by type inference only requires *reachable*
    // code to be valid. For example, `iconst_0; astore_0` is valid in unreachable code in old
    // classfiles, but not new ones.
    //
    // Since we want to parse old classfiles, we have to track reachability and only generate IR
    // from reachable code. We could skip this check for new classfiles, but emitting unreachable
    // code can confuse future passes, so it makes sense to do this unconditionally.
    //
    // A particularly interesting case is exception handlers. An exception handler is only
    // considered reachable in old classfiles if any instruction within its range is reachable (even
    // `nop` works). This interpretation is reasonable for future IRs, with the exception of no-op
    // `try` blocks possibly being optimized out in later passes. But that's a problem for future
    // us, and this pass does not need to concern itself with it.

    // Calculate reachability and stack sizes via DFS, starting with the first BB. We also validate
    // that all instruction ranges are correct and don't stop in the middle of an instruction.
    let mut dfs_stack = vec![0];
    let mut in_stack = vec![false; basic_blocks.len()];
    in_stack[0] = true;
    let mut remaining_eh = IntervalTree::new(
        basic_blocks.len(),
        exception_handlers
            .iter()
            .enumerate()
            .map(|(handler_id, handler)| (handler_id, handler.active_range.clone())),
    );
    while let Some(bb_id) = dfs_stack.pop() {
        let bb = &basic_blocks[bb_id];

        let mut stack_size_at_end = bb.stack_size_at_start.get() as isize;
        let mut reached_end_of_stream = true;

        for row in code.raw_instructions_from(Index::new(bb.instruction_range.start))? {
            let (address, insn) = row?;
            if address.as_u32() == bb.instruction_range.end {
                reached_end_of_stream = false;
                break;
            } else if address.as_u32() > bb.instruction_range.end {
                return Err(BytecodePreparsingError::SplitInstruction);
            }
            stack_size_at_end += get_insn_stack_effect(cpool, &insn)?;
        }
        let stack_size_at_end: usize = stack_size_at_end
            .try_into()
            .map_err(|_| BytecodePreparsingError::StackUnderflow)?;

        if reached_end_of_stream && bb.instruction_range.end != code.byte_len() {
            // This can also be a jump into the middle of the last instruction (which is also
            // erroneous), but we don't have an easy way to disambiguate that.
            return Err(BytecodePreparsingError::CodeFallthrough);
        }

        let successors = basic_blocks[bb_id]
            .successors
            .iter()
            .map(|succ_bb_id| (*succ_bb_id, stack_size_at_end))
            .chain(remaining_eh.drain_containing(bb_id).map(|handler_id| {
                exception_handlers[handler_id].is_reachable = true;
                (exception_handlers[handler_id].target, 1)
            }));

        for (succ_bb_id, stack_size) in successors {
            if succ_bb_id == basic_blocks.len() {
                return Err(BytecodePreparsingError::CodeFallthrough);
            }

            if !in_stack[succ_bb_id] {
                basic_blocks[succ_bb_id].stack_size_at_start.set(stack_size);
                dfs_stack.push(succ_bb_id);
                in_stack[succ_bb_id] = true;
            }
            if basic_blocks[succ_bb_id].stack_size_at_start.get() != stack_size {
                return Err(BytecodePreparsingError::InconsistentStackSize);
            }
        }
    }

    // Erase unreachable BBs. We don't really remove them from this list, since that would affect BB
    // IDs, but we clean them up just enough that they're guaranteed not to refer to invalid
    // bytecode, which could cause problems in future passes.
    for (in_stack, bb) in in_stack.iter().zip(&mut basic_blocks) {
        if !in_stack {
            *bb = BasicBlock {
                instruction_range: 0..0,
                stack_size_at_start: Cell::new(0),
                successors: Vec::new(),
            };
        }
    }
    // Erase unused exception handlers.
    exception_handlers.retain(|handler| handler.is_reachable);

    Ok(Program {
        basic_blocks,
        exception_handlers,
    })
}
