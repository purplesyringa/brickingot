mod abstract_eval;
mod build;
mod insn_ir_import;
mod linking;
mod splitting;

use self::abstract_eval::SealedBlock;
pub use self::build::{StacklessIrError, build_stackless_ir};
use crate::ast::{Arena, BasicStatement, DebugIr, ExprId, Str};
use core::fmt::{self, Display};
use core::ops::Range;
use noak::MStr;

#[derive(Debug)]
pub struct Program<'code> {
    pub statements: Vec<Statement>,
    pub basic_blocks: Vec<BasicBlock>,
    pub exception_handlers: Vec<ExceptionHandler<'code>>,
}

impl<'code> DebugIr<'code> for Program<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        for (i, stmt) in self.statements.iter().enumerate() {
            writeln!(f, "{i}: {}", arena.debug(stmt))?;
        }
        for handler in &self.exception_handlers {
            writeln!(f, "{handler}")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum Statement {
    Basic(BasicStatement),
    Label,
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
            Self::Label => write!(f, "label;"),
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
pub struct BasicBlock {
    pub stmt_range: Range<usize>,
    /// Excludes throwing locations that call into this BB for exception handling.
    pub predecessors: Vec<usize>,
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

struct InternalBasicBlock {
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
