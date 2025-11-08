mod exceptions;
mod gap_tracker;
mod solver;
mod structurizer;

pub use self::structurizer::structure_control_flow;
use crate::ast::{IrDef, StmtList};
use core::ops::Range;
use displaydoc::Display;

pub struct Ir;

impl IrDef for Ir {
    type BasicMeta = IndexMeta;
    type ContinueMeta = IndexMeta;
    type BreakMeta = IndexMeta;
    type SwitchMeta = IndexMeta;
    type CatchMeta = CatchMeta;
}

pub type Program = StmtList<Ir>;

#[derive(Clone, Copy, Debug, Display)]
/// {index}
pub struct IndexMeta {
    index: Index,
}

impl IndexMeta {
    pub fn synthetic() -> Self {
        Self {
            index: Index::Synthetic,
        }
    }
}

#[derive(Clone, Copy, Debug, Display)]
pub enum Index {
    // An auto-generated non-throwing statement not linked to any position in the source code.
    /// .syn
    Synthetic,
    // Produced from the statement at the given position in the linear IR.
    /// .{0}
    Real(usize),
}

#[derive(Debug, Display)]
/// in {active_index_ranges:?},
pub struct CatchMeta {
    pub active_index_ranges: Vec<Range<usize>>,
}
