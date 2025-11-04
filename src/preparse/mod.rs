mod basic_blocks;
mod exceptions;
pub mod insn_control_flow;
pub mod insn_stack_effect;

use self::basic_blocks::extract_basic_blocks;
use self::exceptions::coalesce_exception_handlers;
use self::insn_stack_effect::InsnStackEffectError;
use crate::ClassInfo;
use crate::ast::Str;
use core::ops::Range;
use noak::error::DecodeError;
use noak::reader::{attributes::Code, cpool::ConstantPool};
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
    /// The number of instructions in the range.
    pub n_instructions: usize,
    /// The size of the stack on entry to this BB, counting double-width elements (`long` and
    /// `double`) as two.
    pub stack_size_at_start: usize,
    /// The IDs of BBs the last instruction in this BB can jump to. This includes fallthrough, but
    /// excludes jumps to exception handlers.
    pub successors: Vec<usize>,
}

pub struct Program<'code> {
    pub basic_blocks: Vec<BasicBlock>,
    pub catch_handlers: Vec<CatchHandler<'code>>,
}

// Corresponds to a single `catch` block. Note that this is not the same thing as a single `try`
// block: if a `try` block is associated with multiple `catch` blocks, there's one such entity per
// `catch`. Such blocks will be merged at a later pass. `finally` is similarly not handled in any
// special manner and is represented by a catch-all block.
//
// The name `CatchHandler` instead of `ExceptionHandler` is chosen to highlight the difference
// between handlers associated with a list of ranges vs a single range. A single `catch` block can
// have multiple `try` ranges because the contents of `finally` blocks are inserted at every exit
// point and are excluded from the cover.
pub struct CatchHandler<'code> {
    /// BBs within which exceptions are captured by this handler.
    pub active_ranges: Vec<Range<usize>>,
    /// BB ID of the `catch` body.
    pub target: usize,
    /// The type of the caught exception, or `None` for any.
    pub class: Option<Str<'code>>,
}

pub fn build_preparse_ir<'code>(
    cpool: &ConstantPool<'code>,
    code: &Code<'code>,
    class_info: &mut ClassInfo<'code>,
) -> Result<Program<'code>, BytecodePreparsingError> {
    let bb_ir = extract_basic_blocks(cpool, code, class_info)?;
    let catch_handlers = coalesce_exception_handlers(bb_ir.exception_handlers);
    Ok(Program {
        basic_blocks: bb_ir.basic_blocks,
        catch_handlers,
    })
}
