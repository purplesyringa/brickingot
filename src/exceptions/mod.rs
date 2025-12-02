mod contexts;
mod parse;

pub use self::parse::parse_try_blocks;
use crate::ast::{IrDef, StmtGroup};
pub use crate::structured::CatchMeta;
use core::fmt;
use core::ops::Range;

pub struct Ir;

impl IrDef for Ir {
    type CatchMeta = CatchMeta;
}

pub type Program = StmtGroup<Ir>;

struct AnalysisIr;

impl IrDef for AnalysisIr {
    type Meta = AnalysisMeta;
    type BlockMeta = AnalysisBlockMeta;
    type CatchMeta = CatchMeta;
}

#[derive(Debug)]
pub struct AnalysisMeta {
    // A "size" of the subtree. Doesn't need to be connected to any "real" size, except that:
    //
    // 1. It must be strictly monotonic over subtrees, i.e. the measure of a node must be strictly
    //    less than the measure of its parent.
    // 2. Isomorphic trees must have equal measures.
    //
    // Ideally, different random trees should also have different measures. Used as an asymptotic
    // optimization for locating `finally` blocks.
    measure: usize,
    // Range of variable accesses located entirely within this statement.
    access_range: Range<usize>,
    is_divergent: bool,
}

impl fmt::Display for AnalysisMeta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "measure={} ", self.measure)?;
        if self.is_divergent {
            write!(f, "divergent ")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct AnalysisBlockMeta {
    has_break: bool,
}

impl fmt::Display for AnalysisBlockMeta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.has_break {
            write!(f, "has_break ")?;
        }
        Ok(())
    }
}
