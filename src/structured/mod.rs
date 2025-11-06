mod exceptions;
mod gap_tracker;
mod solver;
mod structurizer;

pub use self::structurizer::structure_control_flow;
use crate::ast::{Arena, BasicStatement, DebugIr, ExprId, Str};
use alloc::fmt;
use core::ops::Range;
use noak::MStr;

#[derive(Debug)]
pub struct Program<'code> {
    pub statements: Vec<Statement<'code>>,
}

#[derive(Debug)]
pub enum Statement<'code> {
    Basic {
        index: Index,
        stmt: BasicStatement,
    },
    Block {
        id: usize,
        children: Vec<Statement<'code>>,
    },
    Continue {
        index: Index,
        block_id: usize,
    },
    Break {
        index: Index,
        block_id: usize,
    },
    If {
        condition: ExprId,
        then_children: Vec<Statement<'code>>,
    },
    Switch {
        index: Index,
        id: usize,
        key: ExprId,
        arms: Vec<(Option<i32>, Vec<Statement<'code>>)>,
    },
    TryCatch {
        try_children: Vec<Statement<'code>>,
        active_index_ranges: Vec<Range<usize>>,
        class: Option<Str<'code>>,
        catch_children: Vec<Statement<'code>>,
    },
}

#[derive(Clone, Copy, Debug)]
pub enum Index {
    /// An auto-generated non-throwing statement not linked to any position in the source code.
    Synthetic,
    /// Produced from the statement at the given position in the linear IR.
    Real(usize),
}

impl<'code> DebugIr<'code> for Program<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        for stmt in &self.statements {
            writeln!(f, "{}", arena.debug(stmt))?;
        }
        Ok(())
    }
}

impl<'code> DebugIr<'code> for Statement<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        match self {
            Self::Basic { index, stmt } => write!(f, "{index} {}", arena.debug(stmt)),

            Self::Block { id, children } => {
                writeln!(f, "block #{id} {{")?;
                for child in children {
                    writeln!(f, "{}", arena.debug(child))?;
                }
                write!(f, "}} block #{id}")
            }

            Self::Continue { index, block_id } => write!(f, "{index} continue #{block_id};"),

            Self::Break { index, block_id } => write!(f, "{index} break #{block_id};"),

            Self::If {
                condition,
                then_children,
            } => {
                writeln!(f, "if ({}) {{", arena.debug(condition))?;
                for child in then_children {
                    writeln!(f, "{}", arena.debug(child))?;
                }
                write!(f, "}}")
            }

            Self::Switch {
                index,
                id,
                key,
                arms,
            } => {
                writeln!(f, "{index} switch #{id} ({}) {{", arena.debug(key))?;
                for (value, children) in arms {
                    match value {
                        Some(value) => writeln!(f, "case {value}:")?,
                        None => writeln!(f, "default:")?,
                    }
                    for child in children {
                        writeln!(f, "{}", arena.debug(child))?;
                    }
                }
                write!(f, "}} switch #{id};")
            }

            Self::TryCatch {
                try_children,
                active_index_ranges,
                class,
                catch_children,
            } => {
                writeln!(f, "try {{")?;
                for child in try_children {
                    writeln!(f, "{}", arena.debug(child))?;
                }
                writeln!(
                    f,
                    "}} catch ({} in {:?}) {{",
                    class.unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
                    active_index_ranges,
                )?;
                for child in catch_children {
                    writeln!(f, "{}", arena.debug(child))?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Synthetic => write!(f, ".syn"),
            Self::Real(index) => write!(f, ".{index}"),
        }
    }
}
