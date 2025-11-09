mod abstract_eval;
mod build;
mod insn_ir_import;
mod linking;
mod splitting;

use self::abstract_eval::SealedBlock;
pub use self::build::{StacklessIrError, build_stackless_ir};
use crate::ast::{Arena, BasicStatement, DebugIr, ExprId, Str, Variable, Version};
use core::fmt;
use core::ops::Range;
use noak::MStr;

#[derive(Debug)]
pub struct Program<'code> {
    pub basic_blocks: Vec<BasicBlock>,
    pub catch_handlers: Vec<CatchHandler<'code>>,
}

impl DebugIr for Program<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result {
        for (bb_id, bb) in self.basic_blocks.iter().enumerate() {
            writeln!(f, "bb{bb_id}:")?;
            for stmt in &bb.statements {
                writeln!(f, "{}", arena.debug(stmt))?;
            }
        }
        for handler in &self.catch_handlers {
            writeln!(f, "{}", arena.debug(handler))?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum Statement {
    Basic(BasicStatement),
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

impl DebugIr for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result {
        match self {
            Self::Basic(stmt) => write!(f, "{}", arena.debug(stmt)),
            Self::Jump { condition, target } => {
                write!(f, "if ({}) goto {target};", arena.debug(condition))
            }
            Self::Switch { key, arms, default } => {
                write!(f, "switch ({}) ", arena.debug(key))?;
                for (value, target) in arms {
                    write!(f, "{value} => goto {target}; ")?;
                }
                write!(f, "default => goto {default};")
            }
        }
    }
}

#[derive(Debug)]
pub struct BasicBlock {
    pub statements: Vec<Statement>,
    /// Excludes throwing locations that call into this BB for exception handling.
    pub predecessors: Vec<usize>,
}

#[derive(Debug)]
pub struct CatchHandler<'code> {
    pub active_ranges: Vec<Range<usize>>,
    pub class: Option<Str<'code>>,
    /// The `valueN` variable the exception is stored in.
    pub value_var: Variable,
    /// If present, the `stack0 = valueN` assignment at the beginning of the body.
    pub stack_value_copy: Option<BasicStatement>,
    /// Where to jump to.
    pub jump_target: usize,
}

impl DebugIr for CatchHandler<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result {
        write!(
            f,
            "try {{ {:?} }} catch ({} {}) {{",
            self.active_ranges,
            self.class
                .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
            self.value_var,
        )?;
        if let Some(stmt) = &self.stack_value_copy {
            write!(f, "{} ", arena.debug(stmt))?;
        }
        write!(f, "goto {} }}", self.jump_target)
    }
}

struct InternalBasicBlock {
    sealed_bb: SealedBlock,
    /// Excludes throwing locations that call into this BB for exception handling.
    predecessors: Vec<usize>,
    eh: Option<ExceptionHandlerBlock>,
}

struct ExceptionHandlerBlock {
    /// The ranges of basic blocks that can jump to the start of this BB on exception.
    eh_entry_for_bb_ranges: Vec<Range<usize>>,
    /// Version of `stack0`, shared among all implicit `stack0 = valueN` statements generated for
    /// `catch` blocks that use this BB as a handler.
    stack_version: Version,
    /// `valueN` in implicit `stack0 = valueN`, if there's a unique `catch` using this BB as
    /// a handler.
    value_var: Option<Variable>,
    stack_value_copy_is_necessary: bool,
}
