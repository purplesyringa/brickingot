mod analysis;
mod contexts;
mod parse;

pub use self::parse::parse_try_blocks;
use crate::ast::{IrDef, StmtGroup};
pub use crate::structured::CatchMeta;

pub struct Ir;

impl IrDef for Ir {
    type CatchMeta = CatchMeta;
}

pub type Program = StmtGroup<Ir>;
