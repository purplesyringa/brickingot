pub mod insn_control_flow;
pub mod insn_stack_effect;

use self::insn_control_flow::{get_insn_control_flow, InsnControlFlow};
use self::insn_stack_effect::{get_insn_stack_effect, InsnStackEffectError};
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
    /// The ranges of instructions that can jump to the start of this BB on exception.
    pub eh_entry_for_ranges: Vec<Range<u32>>,
}

pub fn extract_basic_blocks(
    cpool: &ConstantPool<'_>,
    code: &Code<'_>,
) -> Result<Vec<BasicBlock>, BytecodePreparsingError> {
    // Insert splits after every explicit jump, at each jump target, and at each exception handler.
    // Also at the end and the beginning for implementation simplicity. Save all non-trivial
    // transitions to build the CFG without reparsing the instructions.
    let mut should_insert_split_here = false;
    let mut splits = vec![0, u32::MAX];
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

    splits.extend(
        code.exception_handlers()
            .map(|handler| handler.handler().as_u32()),
    );

    splits.sort();
    splits.dedup();

    // For malformed bytecode, splits can be in the middle of instructions. We'll have verified the
    // correctness by the end of this function during DFS.
    let mut basic_blocks: Vec<BasicBlock> = splits
        .windows(2)
        .enumerate()
        .map(|(bb_id, range)| BasicBlock {
            instruction_range: range[0]..range[1],
            stack_size_at_start: 0,
            successors: vec![bb_id + 1], // We'll remove this for divergent control flow in a moment
            eh_entry_for_ranges: Vec::new(),
        })
        .collect();

    // Fill BB successors
    let mut bb_id = 0;
    for (address, control_flow) in transitions {
        while address >= basic_blocks[bb_id].instruction_range.end {
            bb_id += 1;
        }

        if !control_flow.can_fallthrough {
            // There can be at most one transition per BB, so this BB is in a pristine state.
            basic_blocks[bb_id].successors.clear();
        }

        for target_address in control_flow.can_jump_to {
            // We could use a hashmap here, but there's usually little enough data that binary
            // search is probably better.
            let target_bb_id = basic_blocks
                .binary_search_by_key(&target_address, |bb| bb.instruction_range.start)
                .expect("jump not to BB start");
            basic_blocks[bb_id].successors.push(target_bb_id);
        }
    }

    for bb in &mut basic_blocks {
        bb.successors.sort();
        bb.successors.dedup();
    }

    // *Typically*, the last BB cannot fallthrough, i.e. jump to the non-existent BB after it. We
    // could just emit the error immediately if it does, but then we would emit a false positive if
    // the last BB is actually unreachable. Delay this decision until DFS.

    // Fill EH info
    let mut eh_entry_bb_ids = Vec::new();
    for handler in code.exception_handlers() {
        let bb_id = basic_blocks
            .binary_search_by_key(&handler.handler().as_u32(), |bb| bb.instruction_range.start)
            .expect("EH not to BB start");
        eh_entry_bb_ids.push(bb_id);
        basic_blocks[bb_id]
            .eh_entry_for_ranges
            .push(handler.start().as_u32()..handler.end().as_u32());
    }

    // Calculate reachability and stack sizes via DFS. The first BB and all exception handling BBs
    // are entrypoints. We also validate that all instruction ranges are correct and don't stop in
    // the middle of an instruction.
    let mut dfs_stack = vec![0];
    let mut in_stack = vec![false; basic_blocks.len()];
    in_stack[0] = true;
    for bb_id in eh_entry_bb_ids {
        if !in_stack[bb_id] {
            basic_blocks[bb_id].stack_size_at_start = 1;
            dfs_stack.push(bb_id);
            in_stack[bb_id] = true;
        }
        if basic_blocks[bb_id].stack_size_at_start != 1 {
            return Err(BytecodePreparsingError::InconsistentStackSize);
        }
    }
    while let Some(bb_id) = dfs_stack.pop() {
        let bb = &basic_blocks[bb_id];

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
        }
        let stack_size_at_end: usize = stack_size_at_end
            .try_into()
            .map_err(|_| BytecodePreparsingError::StackUnderflow)?;

        if reached_end_of_stream && bb.instruction_range.end != u32::MAX {
            // This can also be a jump into the middle of the last instruction, but we don't have
            // an easy way to disambiguate that.
            return Err(BytecodePreparsingError::CodeFallthrough);
        }

        for i in 0..basic_blocks[bb_id].successors.len() {
            // This is stupid, but I don't want to fight borrowck here, and adding cells to the API
            // sounds even worse.
            let succ_bb_id = basic_blocks[bb_id].successors[i];

            if succ_bb_id == basic_blocks.len() {
                return Err(BytecodePreparsingError::CodeFallthrough);
            }

            if !in_stack[succ_bb_id] {
                basic_blocks[succ_bb_id].stack_size_at_start = stack_size_at_end;
                dfs_stack.push(succ_bb_id);
                in_stack[succ_bb_id] = true;
            }
            if basic_blocks[succ_bb_id].stack_size_at_start != stack_size_at_end {
                return Err(BytecodePreparsingError::InconsistentStackSize);
            }
        }
    }

    // Erase unreachable BBs. We don't really remove them from this list, but we clean them up just
    // enough that they're guaranteed not to refer to invalid bytecode, which could cause problems
    // in future passes.
    for (in_stack, bb) in in_stack.iter().zip(&mut basic_blocks) {
        if !in_stack {
            *bb = BasicBlock {
                instruction_range: 0..0,
                stack_size_at_start: 0,
                successors: Vec::new(),
                eh_entry_for_ranges: Vec::new(),
            };
        }
    }

    Ok(basic_blocks)
}
