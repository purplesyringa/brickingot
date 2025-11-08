mod arena;
mod debug;
mod expression;
mod iterate;
mod statement;
mod str;

pub use self::arena::{Arena, ExprId};
pub use self::debug::DebugIr;
pub use self::expression::*;
pub use self::statement::{BasicStatement, Catch, IrDef, Statement, StmtList, StmtMeta};
pub use self::str::{Str, String};

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
