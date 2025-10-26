mod abstract_eval;
mod build;
mod exceptions;
mod insn_ir_import;
mod linking;
mod splitting;

use self::abstract_eval::SealedBlock;
pub use self::build::{StacklessIrError, build_stackless_ir};
pub use self::exceptions::legalize_exception_handling;
use crate::ast::{Arena, BasicStatement, DebugIr, ExprId, Str};
use core::fmt;
use core::ops::Range;
use noak::MStr;

#[derive(Debug)]
pub struct Program<'code> {
    pub basic_blocks: Vec<BasicBlock>,
    pub exception_handlers: Vec<ExceptionHandler<'code>>,
}

impl<'code> DebugIr<'code> for Program<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        for (bb_id, bb) in self.basic_blocks.iter().enumerate() {
            writeln!(f, "bb{bb_id}:")?;
            for stmt in &bb.statements {
                writeln!(f, "{}", arena.debug(stmt))?;
            }
        }
        for handler in &self.exception_handlers {
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

impl<'code> DebugIr<'code> for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
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
pub struct ExceptionHandler<'code> {
    pub active_range: Range<usize>,
    pub class: Option<Str<'code>>,
    pub body: EhBody,
}

/// What to do on exception. Basically just the body of `catch`, but very limited structurally,
// since we still  don't have structured control flow, but also don't want to create auxiliary BBs
// just for the `catch` body, so we can't create the logic we want. It'll be rewritten to normal
// code eventually.
#[derive(Debug)]
pub struct EhBody {
    /// The condition under which this catch should be performed.
    pub condition: Option<ExprId>,
    /// The version of `exception0` available within this body. Note that it's not the `exception0`
    /// expression itself, just the version that can be used to create it.
    pub exception0_use: ExprId,
    /// If present, the `stack0 = exception0` assignment in this body.
    pub stack0_exception0_copy: Option<BasicStatement>,
    /// Where to jump to.
    pub jump_target: usize,
}

impl<'code> DebugIr<'code> for ExceptionHandler<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        write!(
            f,
            "try {{ {:?} }} catch ({}",
            self.active_range,
            self.class
                .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
        )?;
        if let Some(condition) = &self.body.condition {
            write!(f, " if {condition:?}")?;
        }
        writeln!(f, ") {{")?;
        if let Some(stmt) = &self.body.stack0_exception0_copy {
            writeln!(f, "{}", arena.debug(stmt))?;
        }
        writeln!(f, "goto {}", self.body.jump_target)?;
        write!(f, "}}")
    }
}

struct InternalBasicBlock {
    statements: Vec<Statement>,
    sealed_bb: SealedBlock,
    /// Excludes throwing locations that call into this BB for exception handling.
    predecessors: Vec<usize>,
    eh: Option<ExceptionHandlerBlock>,
}

struct ExceptionHandlerBlock {
    /// The ranges of basic blocks that can jump to the start of this BB on exception.
    eh_entry_for_bb_ranges: Vec<Range<usize>>,
    /// stack0 in implicit `stack0 = exception0`.
    stack0_def: ExprId,
    /// exception0 in implicit `stack0 = exception0`.
    exception0_use: ExprId,
    stack0_exception0_copy_is_necessary: bool,
}
