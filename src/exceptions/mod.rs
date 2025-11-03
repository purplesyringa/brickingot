mod contexts;
mod parse;

pub use self::parse::parse_try_blocks;
use crate::ast::{Arena, BasicStatement, DebugIr, ExprId, Str};
use alloc::fmt;
use noak::MStr;

#[derive(Debug)]
pub struct Program<'code> {
    pub statements: Vec<Statement<'code>>,
}

#[derive(Debug)]
pub enum Statement<'code> {
    Basic(BasicStatement),
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
        then_children: Vec<Statement<'code>>,
    },
    Switch {
        id: usize,
        key: ExprId,
        arms: Vec<(Option<i32>, Vec<Statement<'code>>)>,
    },
    Try {
        try_children: Vec<Statement<'code>>,
        catches: Vec<Catch<'code>>,
        finally_children: Vec<Statement<'code>>,
    },
}

#[derive(Debug)]
pub struct Catch<'code> {
    pub class: Option<Str<'code>>,
    pub children: Vec<Statement<'code>>,
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
            Self::Basic(stmt) => write!(f, "{}", arena.debug(stmt)),

            Self::Block { id, children } => {
                writeln!(f, "block #{id} {{")?;
                for child in children {
                    writeln!(f, "{}", arena.debug(child))?;
                }
                write!(f, "}} block #{id}")
            }

            Self::Continue { block_id } => write!(f, "continue #{block_id};"),

            Self::Break { block_id } => write!(f, "break #{block_id};"),

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

            Self::Switch { id, key, arms } => {
                writeln!(f, "switch #{id} ({}) {{", arena.debug(key))?;
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

            Self::Try {
                try_children,
                catches,
                finally_children,
            } => {
                writeln!(f, "try {{")?;
                for child in try_children {
                    writeln!(f, "{}", arena.debug(child))?;
                }
                for catch in catches {
                    writeln!(
                        f,
                        "}} catch ({}) {{",
                        catch
                            .class
                            .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
                    )?;
                    for child in &catch.children {
                        writeln!(f, "{}", arena.debug(child))?;
                    }
                }
                if !finally_children.is_empty() {
                    writeln!(f, "}} finally {{")?;
                    for child in finally_children {
                        writeln!(f, "{}", arena.debug(child))?;
                    }
                }
                write!(f, "}}")
            }
        }
    }
}
