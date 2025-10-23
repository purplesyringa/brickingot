pub mod insn_control_flow;
pub mod insn_stack_effect;

use self::insn_control_flow::{InsnControlFlow, can_insn_throw, get_insn_control_flow};
use self::insn_stack_effect::{InsnStackEffectError, get_insn_stack_effect};
use crate::ast::Str;
use crate::utils::IntervalTree;
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
    /// `double`) as two.
    pub stack_size_at_start: usize,
    /// The IDs of BBs the last instruction in this BB can jump to. This includes fallthrough, but
    /// excludes jumps to exception handlers.
    pub successors: Vec<usize>,
    /// Whether any instruction within the basic block can throw.
    throws: bool,
}

pub struct Program<'code> {
    pub basic_blocks: Vec<BasicBlock>,
    pub exception_handlers: Vec<ExceptionHandler<'code>>,
}

pub struct ExceptionHandler<'code> {
    pub active_range: Range<usize>, // BB IDs
    pub target: usize,              // BB ID
    pub class: Option<Str<'code>>,
    is_reachable: bool,
    tail_is_reachable: bool, // whether there is a throwing reachable BB in the `target..end` range
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
            stack_size_at_start: 0, // will be populated in a bit
            // `successors` can only be populated after BB boundaries have been decided, so this
            // stays in a sentinel-like state where only the trivial successor is recorded. We'll
            // remove it for divergent control flow a bit later.
            successors: vec![bb_id + 1],
            throws: false,
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
            //
            // It's a bit unusual that we unconditionally add a fallthrough successor and then
            // conditionally remove it, instead of just conditionally adding it. That's because
            // there isn't necessarily a transition after each BB, if that BB was split in the
            // middle by e.g. a `try` boundary.
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
            tail_is_reachable: false,
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

    // I know this looks ridiculous.
    //
    // The accidental complexity comes, as always, from others' code. The problem we're dealing with
    // here is that javac is bollocks and occasionally generates longer `try` ranges than
    // reasonable. Specifically, `try..catch..finally` generates, among other ranges, a range
    // covering `catch` blocks and the *first instruction* of the `finally` handler. This means that
    // `target` ends up being inside `start..end`, resulting in a mess in the decompiled output.
    //
    // We fix this by moving `end` backward to `target` if all BBs in range `[target; end)` don't
    // contain throwing instructions. This is specific enough that it shouldn't break anything else,
    // including other codegen backends, and it's wide enough to reliably fix this particular
    // problem.
    //
    // Unfortunately, this can affect reachability. The concern is that if the only reachable BBs
    // are in range `[target; end)`, and none of them throw, we shouldn't recurse into the `catch`
    // handler. To integrate this logic into DFS, we have to differentiate between throwing BBs,
    // which make the `catch` reachable within the whole range, and non-throwing BBs, which only
    // make it reachable in range `[start; target)`. This guarantees that the reachability graph is
    // completely consistent with the exception ranges.

    let [mut remaining_eh, mut remaining_eh_throwing] = [
        // Applies to all BBs.
        |handler: &ExceptionHandler<'_>| {
            handler.active_range.start..handler.active_range.end.min(handler.target)
        },
        // Applies only to throwing BBs.
        |handler: &ExceptionHandler<'_>| {
            handler.active_range.start.max(handler.target)..handler.active_range.end
        },
    ]
    .map(|range_fn| {
        IntervalTree::new(
            basic_blocks.len(),
            exception_handlers
                .iter()
                .enumerate()
                .map(|(handler_id, handler)| (handler_id, range_fn(handler))),
        )
    });

    while let Some(bb_id) = dfs_stack.pop() {
        let bb = &mut basic_blocks[bb_id];

        let mut stack_size_at_end = bb.stack_size_at_start as isize;
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
            bb.throws |= can_insn_throw(&insn);
        }
        let stack_size_at_end: usize = stack_size_at_end
            .try_into()
            .map_err(|_| BytecodePreparsingError::StackUnderflow)?;

        if reached_end_of_stream && bb.instruction_range.end != code.byte_len() {
            // This can also be a jump into the middle of the last instruction (which is also
            // erroneous), but we don't have an easy way to disambiguate that.
            return Err(BytecodePreparsingError::CodeFallthrough);
        }

        // Help borrowck. Don't forget to restore `bb.successors` afterwards.
        let tmp_successors = core::mem::take(&mut bb.successors);
        {
            let explicit_successors = tmp_successors
                .iter()
                .map(|succ_bb_id| (*succ_bb_id, stack_size_at_end));

            let eh_successors = remaining_eh
                .drain_containing(bb_id)
                .map(|handler_id| (handler_id, false))
                .chain(
                    bb.throws
                        .then(|| {
                            remaining_eh_throwing
                                .drain_containing(bb_id)
                                .map(|handler_id| (handler_id, true))
                        })
                        .into_iter()
                        .flatten(),
                )
                .map(|(handler_id, is_tail)| {
                    let handler = &mut exception_handlers[handler_id];
                    handler.is_reachable = true;
                    if is_tail {
                        handler.tail_is_reachable = true;
                    }
                    (handler.target, 1)
                });

            for (succ_bb_id, stack_size) in explicit_successors.chain(eh_successors) {
                if succ_bb_id == basic_blocks.len() {
                    return Err(BytecodePreparsingError::CodeFallthrough);
                }

                if !in_stack[succ_bb_id] {
                    basic_blocks[succ_bb_id].stack_size_at_start = stack_size;
                    dfs_stack.push(succ_bb_id);
                    in_stack[succ_bb_id] = true;
                }
                if basic_blocks[succ_bb_id].stack_size_at_start != stack_size {
                    return Err(BytecodePreparsingError::InconsistentStackSize);
                }
            }
        }
        basic_blocks[bb_id].successors = tmp_successors;
    }

    // Erase unreachable BBs. We don't really remove them from this list, since that would affect BB
    // IDs, but we clean them up just enough that they're guaranteed not to refer to invalid
    // bytecode, which could cause problems in future passes.
    for (in_stack, bb) in in_stack.iter().zip(&mut basic_blocks) {
        if !in_stack {
            *bb = BasicBlock {
                instruction_range: 0..0,
                stack_size_at_start: 0,
                successors: Vec::new(),
                throws: false,
            };
        }
    }
    // Erase unused exception handlers.
    exception_handlers.retain(|handler| handler.is_reachable);
    // Truncate the exception handler.
    for handler in &mut exception_handlers {
        if !handler.tail_is_reachable && handler.target < handler.active_range.end {
            handler.active_range.end = handler.target;
        }
    }

    Ok(Program {
        basic_blocks,
        exception_handlers,
    })
}
