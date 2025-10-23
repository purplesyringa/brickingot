mod arena;
mod debug;
mod expression;
mod iterate;

pub use self::arena::{Arena, ExprId};
pub use self::debug::DebugIr;
pub use self::expression::*;
use core::fmt;

#[derive(Debug)]
pub enum BasicStatement {
    Assign { target: ExprId, value: ExprId },
    Return { value: ExprId },
    ReturnVoid,
    Throw { exception: ExprId },
    Calculate(ExprId),
    MonitorEnter { object: ExprId },
    MonitorExit { object: ExprId },
}

impl<'code> DebugIr<'code> for BasicStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        match self {
            Self::Assign { target, value } => {
                write!(f, "{} = {};", arena.debug(target), arena.debug(value))
            }
            Self::Return { value } => write!(f, "return {};", arena.debug(value)),
            Self::ReturnVoid => write!(f, "return;"),
            Self::Throw { exception } => write!(f, "throw {};", arena.debug(exception)),
            Self::Calculate(value) => write!(f, "{};", arena.debug(value)),
            Self::MonitorEnter { object } => write!(f, "lock {};", arena.debug(object)),
            Self::MonitorExit { object } => write!(f, "unlock {};", arena.debug(object)),
        }
    }
}

impl BasicStatement {
    pub fn is_divergent(&self) -> bool {
        match self {
            Self::Assign { .. }
            | Self::Calculate(_)
            | Self::MonitorEnter { .. }
            | Self::MonitorExit { .. } => false,
            Self::Return { .. } | Self::ReturnVoid | Self::Throw { .. } => true,
        }
    }
}
