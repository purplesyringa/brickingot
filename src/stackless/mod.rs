mod abstract_eval;
mod build;
mod insn_ir_import;
mod linking;
mod splitting;

use self::abstract_eval::SealedBlock;
pub use self::build::{StacklessIrError, build_stackless_ir};
use crate::arena::{Arena, DebugIr, ExprId};
use crate::ast::{BasicStatement, Str};
use core::fmt::{self, Display};
use core::ops::Range;
use noak::MStr;

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

struct BasicBlock {
    sealed_bb: SealedBlock,
    /// Excludes throwing locations that call into this BB for exception handling.
    predecessors: Vec<usize>,
    eh: Option<ExceptionHandlerBlock>,
}

struct ExceptionHandlerBlock {
    eh_entry_for_bb_ranges: Vec<Range<usize>>,
    // stack0 in implicit `stack0 = exception0`.
    stack0_def: ExprId,
    // exception0 in implicit `stack0 = exception0`.
    exception0_use: ExprId,
    stack0_exception0_copy_is_necessary: bool,
}
