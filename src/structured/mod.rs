mod gap_tracker;
mod interval_tree;
mod solver;
mod structurizer;

pub use self::structurizer::structure_control_flow;
use crate::arena::{Arena, DebugIr, ExprId};
use crate::ast::{BasicStatement, Str};
use alloc::fmt;
use core::ops::Range;
use noak::MStr;

#[derive(Debug)]
pub enum Statement<'code> {
    Basic {
        // In this IR, only basic statements can throw, since other statements are constructed with
        // trivial expressions and inlining hasn't occurred yet. This allows us to keep track of
        // exception origins simply by tracking the last basic statement executed before entry to
        // `catch`. `None` for synthetic never-throwing statements.
        index: Option<usize>,
        stmt: BasicStatement,
    },
    Block {
        id: usize,
        children: Vec<Statement<'code>>,
    },
    Continue {
        block_id: usize,
    },
    Break {
        block_id: usize,
    },
    If {
        condition: ExprId,
        // This could be simulated by swapping `then_children` and `else_children`, but that
        // reorders statements and thus complicates AST optimization. It could also be implemented
        // by updating `condition`, but we occasionally need to invert conditions several times, and
        // just flicking a bool is simpler.
        condition_inverted: bool,
        then_children: Vec<Statement<'code>>,
        else_children: Vec<Statement<'code>>,
    },
    Switch {
        id: usize,
        key: ExprId,
        arms: Vec<(Option<i32>, Vec<Statement<'code>>)>,
    },
    Try {
        children: Vec<Statement<'code>>,
        catches: Vec<Catch<'code>>,
    },
}

#[derive(Debug)]
pub struct Catch<'code> {
    pub class: Option<Str<'code>>,
    pub children: Vec<Statement<'code>>,
    pub active_range: Range<usize>,
}

impl<'code> DebugIr<'code> for Statement<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        match self {
            Self::Basic { index, stmt } => {
                if let Some(index) = index {
                    write!(f, "#{index} ")?;
                }
                write!(f, "{}", arena.debug(stmt))
            }

            Self::Block { id, children } => {
                write!(f, "block #{id} {{\n")?;
                for child in children {
                    write!(f, "{}\n", arena.debug(child))?;
                }
                write!(f, "}} block #{id}")
            }

            Self::Continue { block_id } => write!(f, "continue #{block_id};"),

            Self::Break { block_id } => write!(f, "break #{block_id};"),

            Self::If {
                condition,
                condition_inverted,
                then_children,
                else_children,
            } => {
                write!(f, "if (")?;
                if *condition_inverted {
                    write!(f, "!({})", arena.debug(condition))?;
                } else {
                    write!(f, "{}", arena.debug(condition))?;
                }
                write!(f, ") {{\n")?;
                for child in then_children {
                    write!(f, "{}\n", arena.debug(child))?;
                }
                if !else_children.is_empty() {
                    write!(f, "}} else {{\n")?;
                    for child in else_children {
                        write!(f, "{}\n", arena.debug(child))?;
                    }
                }
                write!(f, "}}")
            }

            Self::Switch { id, key, arms } => {
                write!(f, "switch #{id} ({}) {{\n", arena.debug(key))?;
                for (value, children) in arms {
                    match value {
                        Some(value) => write!(f, "case {value}:\n")?,
                        None => write!(f, "default:\n")?,
                    }
                    for child in children {
                        write!(f, "{}\n", arena.debug(child))?;
                    }
                }
                write!(f, "}} switch #{id};")
            }

            Self::Try { children, catches } => {
                write!(f, "try {{\n")?;
                for child in children {
                    write!(f, "{}\n", arena.debug(child))?;
                }
                for catch in catches {
                    write!(
                        f,
                        "}} catch ({} within {:?}) {{\n",
                        catch
                            .class
                            .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
                        catch.active_range
                    )?;
                    for child in &catch.children {
                        write!(f, "{}\n", arena.debug(child))?;
                    }
                }
                write!(f, "}}")
            }
        }
    }
}
