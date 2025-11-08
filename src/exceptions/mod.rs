mod contexts;
mod parse;

pub use self::parse::parse_try_blocks;
use crate::ast::{IrDef, StmtList};
use core::ops::Range;
use displaydoc::Display;

pub struct Ir;

impl IrDef for Ir {
    type CatchMeta = CatchMeta;
}

pub type Program = StmtList<Ir>;

#[derive(Debug, Display)]
/// in {active_index_ranges:?},
pub struct CatchMeta {
    active_index_ranges: Vec<Range<usize>>,
}
