mod inlining;
mod main_opt;

use self::main_opt::optimize;
use crate::ast::{Arena, BasicStatement, DebugIr, ExprId, Str};
use crate::structured;
use alloc::fmt;
use core::ops::Range;
use noak::MStr;

#[derive(Debug)]
enum Statement<'code> {
    Basic(BasicStatement),
    Block {
        id: usize,
        children: StmtList<'code>,
    },
    Continue {
        block_id: usize,
    },
    Break {
        block_id: usize,
    },
    If {
        condition: ExprId,
        // We use this to reorder statements closer to source without patching `condition`, since we
        // may need to invert it multiple times, and flicking a bool is simpler.
        condition_inverted: bool,
        then_children: StmtList<'code>,
        else_children: StmtList<'code>,
    },
    Switch {
        id: usize,
        key: ExprId,
        arms: Vec<(Option<i32>, StmtList<'code>)>,
    },
    Try {
        children: StmtList<'code>,
        catches: Vec<Catch<'code>>,
    },
}

#[derive(Debug)]
struct Catch<'code> {
    class: Option<Str<'code>>,
    children: StmtList<'code>,
    active_range: Range<usize>,
}

#[derive(Debug, Default)]
struct Meta {
    is_divergent: bool,
    first_uninlined_switch_arm: usize,
    n_breaks_from_switch: usize,
}

#[derive(Debug)]
pub struct StmtMeta<'code> {
    stmt: Statement<'code>,
    meta: Meta,
}

type StmtList<'code> = Vec<StmtMeta<'code>>;

impl<'code> DebugIr<'code> for StmtMeta<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        write!(f, "{}{}", arena.debug(&self.meta), arena.debug(&self.stmt))
    }
}

impl<'code> DebugIr<'code> for Meta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, _arena: &Arena<'code>) -> fmt::Result {
        if self.is_divergent {
            write!(f, "!divergent ")?;
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
                condition_inverted,
                then_children,
                else_children,
            } => {
                write!(f, "if (")?;
                if *condition_inverted {
                    write!(f, "!(")?;
                }
                write!(f, "{}", arena.debug(condition))?;
                if *condition_inverted {
                    write!(f, ")")?;
                }
                writeln!(f, ") {{")?;
                for child in then_children {
                    writeln!(f, "{}", arena.debug(child))?;
                }
                if !else_children.is_empty() {
                    writeln!(f, "}} else {{")?;
                    for child in else_children {
                        writeln!(f, "{}", arena.debug(child))?;
                    }
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

            Self::Try { children, catches } => {
                writeln!(f, "try {{")?;
                for child in children {
                    writeln!(f, "{}", arena.debug(child))?;
                }
                for catch in catches {
                    writeln!(
                        f,
                        "}} catch ({} within {:?}) {{",
                        catch
                            .class
                            .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
                        catch.active_range
                    )?;
                    for child in &catch.children {
                        writeln!(f, "{}", arena.debug(child))?;
                    }
                }
                write!(f, "}}")
            }
        }
    }
}

pub fn decompile_cf_constructs<'code>(
    arena: &mut Arena<'code>,
    structured_ir: Vec<structured::Statement<'code>>,
) -> Vec<StmtMeta<'code>> {
    // The general approach here is to consider a high-level Java control flow construct, find the
    // properties that all of its lowerings are guaranteed to have, and tweak them such that either
    // there are no false positive matches, or all false positives are documented and can be
    // accounted for.

    // Perhaps the most important problem during this stage is determining whether a sequence of
    // statements can be simplified to a single expression. This is necessary to recognize
    // conditions of `while` loops, to translate `if` into `?:` (which in turn determines whether
    // other sequences can be simplified), and to handle `&&`/`||` chains.
    //
    // We perform the bulk of the work necessary to answer this question in a single pass. This
    // includes decompiling `if` statements and Java features lowering to loops, like `switch`
    // expressions with guarded patterns. It also allows us not to think too hard about fixpointing
    // and making sure earlier passes don't make possibly suboptimal decisions that might impact
    // later passes.
    //
    // The above implies that this pass must convert statements into a single `Assign` if that's
    // possible; but if it's not, basically no requirements are made regarding the pass output. This
    // allows unused blocks, no-op `break`/`continue`, etc., which are hard to fix up in a single
    // pass.
    optimize(arena, structured_ir)
}
