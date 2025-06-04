use crate::arrows::{Arrow, ArrowKind};
use crate::ast::{BasicStatement, Expression, VariableNamespace};
use crate::unstructured::{self};
use core::fmt::{self, Display};
use core::ops::Range;
use std::collections::HashMap;

#[derive(Debug)]
pub enum Statement<'a> {
    Basic(BasicStatement<'a>),
    Block {
        id: usize,
        children: Vec<Statement<'a>>,
    },
    DoWhile {
        id: usize,
        condition: Box<Expression<'a>>,
        // This could be simulated by swapping `then_children` and `else_children`, but that
        // reorders statements and thus complicates AST optimization. It could also be implemented
        // by updating `condition`, but we occasionally need to invert conditions several times, and
        // just flicking a bool is simpler.
        condition_inverted: bool,
        children: Vec<Statement<'a>>,
    },
    While {
        id: usize,
        condition: Box<Expression<'a>>,
        condition_inverted: bool,
        children: Vec<Statement<'a>>,
    },
    If {
        condition: Box<Expression<'a>>,
        condition_inverted: bool,
        then_children: Vec<Statement<'a>>,
        else_children: Vec<Statement<'a>>,
    },
    Switch {
        id: usize,
        key: Box<Expression<'a>>,
        arms: Vec<(Option<i32>, Vec<Statement<'a>>)>,
    },
    Continue {
        block_id: usize,
    },
    Break {
        block_id: usize,
    },
    // Try {
    //     children: Vec<Statement<'a>>,
    //     catches: Vec<Catch<'a>>,
    // },
    // TryRangeMarker {
    //     id: usize,
    // },
}

// #[derive(Debug)]
// pub struct Catch<'a> {
//     pub class: Option<Str<'a>>,
//     pub children: Vec<Statement<'a>>,
//     pub active_range: Range<usize>,
// }

impl Display for Statement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Basic(basic) => write!(f, "{basic}"),

            Self::Block { id, children } => {
                write!(f, "block #{id} {{\n")?;
                for child in children {
                    write!(f, "{child}\n")?;
                }
                write!(f, "}} block #{id};")
            }

            Self::DoWhile {
                id,
                condition,
                condition_inverted,
                children,
            } => {
                write!(f, "do #{id} {{\n")?;
                for child in children {
                    write!(f, "{child}\n")?;
                }
                write!(f, "}} while (")?;
                if *condition_inverted {
                    write!(f, "!({condition})")?;
                } else {
                    write!(f, "{condition}")?;
                }
                write!(f, ") #{id};")
            }

            Self::While {
                id,
                condition,
                condition_inverted,
                children,
            } => {
                write!(f, "while #{id} (")?;
                if *condition_inverted {
                    write!(f, "!({condition})")?;
                } else {
                    write!(f, "{condition}")?;
                }
                write!(f, ") {{\n")?;
                for child in children {
                    write!(f, "{child}\n")?;
                }
                write!(f, "}} while #{id};")
            }

            Self::If {
                condition,
                condition_inverted,
                then_children,
                else_children,
            } => {
                write!(f, "if (")?;
                if *condition_inverted {
                    write!(f, "!({condition})")?;
                } else {
                    write!(f, "{condition}")?;
                }
                write!(f, ") {{\n")?;
                for child in then_children {
                    write!(f, "{child}\n")?;
                }
                if !else_children.is_empty() {
                    write!(f, "}} else {{\n")?;
                    for child in else_children {
                        write!(f, "{child}\n")?;
                    }
                }
                write!(f, "}}")
            }

            Self::Switch { id, key, arms } => {
                write!(f, "switch #{id} ({key}) {{\n")?;
                for (value, children) in arms {
                    match value {
                        Some(value) => write!(f, "case {value}:\n")?,
                        None => write!(f, "default:\n")?,
                    }
                    for child in children {
                        write!(f, "{child}\n")?;
                    }
                }
                write!(f, "}} switch #{id};")
            }

            Self::Continue { block_id } => write!(f, "continue #{block_id};"),

            Self::Break { block_id } => write!(f, "break #{block_id};"),
            // Self::Try { children, catches } => {
            //     write!(f, "try {{\n")?;
            //     for child in children {
            //         write!(f, "{child}\n")?;
            //     }
            //     for catch in catches {
            //         write!(
            //             f,
            //             "}} catch ({} within {:?}) {{\n",
            //             catch
            //                 .class
            //                 .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
            //             catch.active_range
            //         )?;
            //         for child in &catch.children {
            //             write!(f, "{child}\n")?;
            //         }
            //     }
            //     write!(f, "}}")
            // }
            // Self::TryRangeMarker { id } => write!(f, "try marker #{id};"),
        }
    }
}

fn make_selector<'a>() -> Box<Expression<'a>> {
    Box::new(Expression::Variable {
        id: 0,
        namespace: VariableNamespace::Selector,
    })
}

struct Context<'a> {
    program_in: unstructured::Program<'a>,
    unresolved_arrows: Vec<Arrow>,
    jump_implementations: HashMap<ArrowKind, JumpImplementation>,
    next_block_id: usize,
    dispatchers: HashMap<usize, Dispatcher>,
}

#[derive(Default)]
struct Dispatcher {
    target_to_selector: HashMap<usize, usize>,
}

impl<'a> Context<'a> {
    fn jump(&self, kind: ArrowKind) -> Vec<Statement<'a>> {
        match *self
            .jump_implementations
            .get(&kind)
            .expect("unresolved jump")
        {
            JumpImplementation::Continue { block_id } => vec![Statement::Continue { block_id }],
            JumpImplementation::Break { block_id } => vec![Statement::Break { block_id }],
            JumpImplementation::ViaDispatcher { block_id, selector } => vec![
                Statement::Basic(BasicStatement::Assign {
                    target: make_selector(),
                    value: Box::new(Expression::ConstInt(
                        // Impossible for bytecode of size < 64k
                        selector.try_into().expect("selector out of bounds"),
                    )),
                }),
                Statement::Continue { block_id },
            ],
        }
    }
}

enum JumpImplementation {
    Continue { block_id: usize },
    Break { block_id: usize },
    ViaDispatcher { block_id: usize, selector: usize },
}

fn parse_multiple_statements<'a>(
    context: &mut Context<'a>,
    range: Range<usize>,
) -> Vec<Statement<'a>> {
    // All unresolved arrows either don't intersect the range at all, or are nested within it. No
    // arrows strictly cover the range. Gaps may be present in the range.

    // Find gaps within range to split by
    let gap = (range.start + 1..range.end).rev().find(|gap| {
        context
            .unresolved_arrows
            .iter()
            .all(|arrow| !(arrow.from.min(arrow.to) + 1..arrow.from.max(arrow.to)).contains(gap))
    });

    let mut stmts = if let Some(gap) = gap {
        parse_multiple_statements(context, range.start..gap)
    } else {
        Vec::new()
    };

    parse_single_structure(context, gap.unwrap_or(range.start)..range.end, &mut stmts);

    stmts
}

fn parse_single_structure<'a>(
    context: &mut Context<'a>,
    range: Range<usize>,
    stmts: &mut Vec<Statement<'a>>,
) {
    // All unresolved arrows either don't intersect the range at all, or are nested within it. No
    // arrows strictly cover the range, although an arrow may exactly match the range. No gaps are
    // present inside the range, but `range` may cover a single statement, either basic or not.

    if range.len() == 1 {
        let mut arrows_covering_stmt = context
            .unresolved_arrows
            .extract_if(.., |arrow| {
                arrow.from.min(arrow.to) == range.start && arrow.from.max(arrow.to) == range.end
            })
            .peekable();

        if arrows_covering_stmt.peek().is_some() {
            let block_id = context.next_block_id;
            context.next_block_id += 1;

            for arrow in arrows_covering_stmt {
                let imp = if arrow.from < arrow.to {
                    JumpImplementation::Break { block_id }
                } else {
                    JumpImplementation::Continue { block_id }
                };
                context.jump_implementations.insert(arrow.kind, imp);
            }

            stmts.push(Statement::Block {
                id: block_id,
                children: parse_multiple_statements(context, range),
            });

            return;
        }

        drop(arrows_covering_stmt);

        // As all dispatch arrows cover the range, they should have already been covered.
        if let Some(dispatch_info) = context.dispatchers.remove(&range.start) {
            let switch_id = context.next_block_id;
            context.next_block_id += 1;

            let mut arms: Vec<(usize, usize)> =
                dispatch_info.target_to_selector.into_iter().collect();
            arms.sort_by_key(|(target, _)| *target);

            stmts.push(Statement::Switch {
                id: switch_id,
                key: make_selector(),
                arms: arms
                    .into_iter()
                    .map(|(_, selector)| {
                        let mut children = vec![Statement::Basic(BasicStatement::Assign {
                            target: make_selector(),
                            value: Box::new(Expression::ConstInt(0)),
                        })];
                        children.extend(context.jump(ArrowKind::Dispatch {
                            stmt_index: range.start,
                            selector,
                        }));
                        (
                            Some(selector.try_into().expect("selector out of bounds")),
                            children,
                        )
                    })
                    .collect(),
            });
        }

        // Need to replace with *something*, `return;` works fine.
        let stmt = core::mem::replace(
            &mut context.program_in.statements[range.start],
            unstructured::Statement::Basic(BasicStatement::ReturnVoid),
        );

        match stmt {
            unstructured::Statement::Basic(stmt) => stmts.push(Statement::Basic(stmt)),
            unstructured::Statement::Jump { condition, .. } => {
                let jump = context.jump(ArrowKind::Jump {
                    stmt_index: range.start,
                });
                if let Expression::ConstInt(1) = *condition {
                    stmts.extend(jump);
                } else {
                    stmts.push(Statement::If {
                        condition,
                        condition_inverted: false,
                        then_children: jump,
                        else_children: Vec::new(),
                    });
                }
            }
            unstructured::Statement::Switch(unstructured::Switch { key, arms, default }) => {
                // Switches are only guaranteed to have a quality lowering if the arms are sorted by
                // target.
                let mut arms: Vec<(Option<i32>, usize)> = core::iter::once((None, default))
                    .chain(arms.iter().map(|(key, target)| (Some(*key), *target)))
                    .collect();
                arms.sort_by_key(|(_, target)| *target);

                let switch_id = context.next_block_id;
                context.next_block_id += 1;
                stmts.push(Statement::Switch {
                    id: switch_id,
                    key,
                    arms: arms
                        .into_iter()
                        .map(|(key, _)| {
                            (
                                key,
                                context.jump(ArrowKind::Switch {
                                    stmt_index: range.start,
                                    key,
                                }),
                            )
                        })
                        .collect(),
                });
            }
        }

        return;
    }

    let block_id = context.next_block_id;
    context.next_block_id += 1;

    for arrow in context.unresolved_arrows.extract_if(.., |arrow| {
        (arrow.from < arrow.to && arrow.to == range.end)
            || (arrow.to < arrow.from && arrow.to == range.start)
    }) {
        let imp = if arrow.from < arrow.to {
            JumpImplementation::Break { block_id }
        } else {
            JumpImplementation::Continue { block_id }
        };
        context.jump_implementations.insert(arrow.kind, imp);
    }

    let forward_gap = (range.start + 1..range.end)
        .find(|gap| {
            context
                .unresolved_arrows
                .iter()
                .filter(|arrow| arrow.from < arrow.to)
                .all(|arrow| !(arrow.from + 1..arrow.to).contains(gap))
        })
        .expect("oops");

    let dispatch_info = context.dispatchers.entry(range.start).or_default();

    for arrow in &mut context.unresolved_arrows {
        if !(arrow.to < arrow.from && (arrow.to + 1..arrow.from).contains(&forward_gap)) {
            continue;
        }

        let next_selector = dispatch_info.target_to_selector.len() + 1;
        let selector = *dispatch_info
            .target_to_selector
            .entry(arrow.to)
            .or_insert(next_selector);
        context.jump_implementations.insert(
            arrow.kind,
            JumpImplementation::ViaDispatcher { block_id, selector },
        );

        arrow.from = range.start;
        arrow.kind = ArrowKind::Dispatch {
            stmt_index: range.start,
            selector,
        };
    }

    if dispatch_info.target_to_selector.is_empty() {
        context.dispatchers.remove(&range.start);
    }

    stmts.push(Statement::Block {
        id: block_id,
        children: parse_multiple_statements(context, range),
    });
}

pub fn structurize_cfg(program_in: unstructured::Program<'_>) -> Vec<Statement<'_>> {
    let mut arrows = Vec::new();

    let mut add_branch = |mut from: usize, to: usize, kind: ArrowKind| {
        // If `from < to`, the statement `from` is within `[from; to)`. But if `from >= to`, `from`
        // is only present within `[to; from + 1)`, so we need to increment `from` so that the gap
        // interval covers the statement.
        if from >= to {
            from += 1;
        }
        arrows.push(Arrow { from, to, kind });
    };

    for (index, stmt) in program_in.statements.iter().enumerate() {
        match stmt {
            unstructured::Statement::Basic(_) => {}
            unstructured::Statement::Jump { target, .. } => {
                add_branch(index, *target, ArrowKind::Jump { stmt_index: index })
            }
            unstructured::Statement::Switch(unstructured::Switch { arms, default, .. }) => {
                for (key, successor) in arms {
                    add_branch(
                        index,
                        *successor,
                        ArrowKind::Switch {
                            stmt_index: index,
                            key: Some(*key),
                        },
                    );
                }
                add_branch(
                    index,
                    *default,
                    ArrowKind::Switch {
                        stmt_index: index,
                        key: None,
                    },
                );
            }
        }
    }

    let range = 0..program_in.statements.len();
    let mut context = Context {
        program_in,
        unresolved_arrows: arrows,
        jump_implementations: HashMap::new(),
        next_block_id: 0,
        dispatchers: HashMap::new(),
    };

    let mut stmts = parse_multiple_statements(&mut context, range);
    if !context.dispatchers.is_empty() {
        stmts.insert(
            0,
            Statement::Basic(BasicStatement::Assign {
                target: make_selector(),
                value: Box::new(Expression::ConstInt(0)),
            }),
        );
    }
    stmts

    // // Exception handlers also affect control flow: we need to be able to travel from any statement
    // // within the `try` block to the exception handler. This is a little harder than it seems,
    // // because adding the minimal arrow containing the guarded statements does not guarantee that we
    // // can wrap the corresponding statements in a single `try` block.
    // //
    // // Consider, for example, the following input program:
    // //
    // //     print a;            \                                        |   : :
    // //     if (...) goto 1;    | try { ... } catch { goto 2; }          | | : :
    // //     print b;            /                                        | | : :
    // //     goto 3;                                                      | v | :
    // // 1:  print c;                                                     |   | :
    // //     goto 3;                                                      v   | |
    // // 2:  print d;                                                         v v
    // // 3:
    // //
    // // ...which is a variant of the following snippet, just with messier control flow, namely
    // // exceptions at `print c;` not being caught:
    // //
    // //     try {
    // //         print a;
    // //         if (!...) {
    // //             print b;
    // //         } else {
    // //             print c;
    // //         }
    // //     } catch {
    // //         print d;
    // //     }
    // //
    // // A `try` block cannot be added around the first three statements because it would get
    // // interleaved with the `goto 1` arrow. We can instead capture the six statements within the
    // // range of the (extended) `try` arrow, which corresponds to the following decompilation:
    // //
    // //     boolean is_in_range = true;
    // //     try {
    // //         print a;
    // //         if (!...) {
    // //             print b;
    // //         } else {
    // //             is_in_range = false;
    // //             print c;
    // //         }
    // //     } catch {
    // //         if (!is_in_range) rethrow;
    // //         print d;
    // //     }
    // //
    // // There a seemingly simpler way to handle this that doesn't introduce synthetic variables. We
    // // could wrap each statement in an individual `try..catch` block and then merge neighboring
    // // `try` blocks together. However this inhibits certain rewrites that significantly simplify
    // // the code in other ways. On the snippet above, such an approach would lead to the following
    // // decompilation:
    // //
    // //     do {
    // //         try {
    // //             print a;
    // //         } catch {
    // //             break;
    // //         }
    // //         do {
    // //             try {
    // //                 if (...) {
    // //                     break;
    // //                 }
    // //                 print b;
    // //             } catch {
    // //                 break 2;
    // //             }
    // //             return;
    // //         } while (false);
    // //         print c;
    // //         return;
    // //     } while (false);
    // //     print d;
    // //
    // // We have to use `break`s in `catch` and add `do { ... } while (false);` to deduplicate the
    // // exception handler, and even if we didn't care about that, `print c;` still needs to be
    // // accessed via a `break;` so that it's outside the `try` block.
    // //
    // // Another nasty problem is the quadratic symptotic complexity of `try` block splitting. `try`
    // // blocks are not guaranteed to nest correctly, and that means that even if two `try` blocks
    // // are nested, the larger one can have priority over the smaller one, and that means that
    // // the exception handling ranges like here:
    // //
    // //     a;   \
    // //     b;   | \
    // //     c;   | | \
    // //     d;   | | | \
    // //     e;   / / / / |
    // //
    // // ...would have to be compiled to:
    // //
    // //     try {
    // //         a;
    // //     } catch { 1 }
    // //     try {
    // //         try {
    // //             b;
    // //         } catch { 1 }
    // //     } catch { 2 }
    // //     try {
    // //         try {
    // //             try {
    // //                 c;
    // //             } catch { 1 }
    // //         } catch { 2 }
    // //     } catch { 3 }
    // //     ...
    // //
    // // Meanwhile, the region tracking approach is linear: we can basically track the index of the
    // // statement currently being evaluated by setting a synthetic variable prior to each statement,
    // // and then check if the index is in range for the exception handler with an O(1)
    // // `const <= synthetic-var < const` comparison. This approach has a runtime cost, but, frankly
    // // speaking, HotSpot doesn't like complex constructs like this one anyway, so the goal here is
    // // just to generate reasonable code.

    // let mut exception_handling_boundaries = Vec::new();

    // for (handler_index, handler) in program_in.exception_handlers.iter().enumerate() {
    //     exception_handling_boundaries.push(handler.start);
    //     exception_handling_boundaries.push(handler.end);

    //     let to = handler.target;
    //     let kind = ArrowKind::Try { handler_index };
    //     if handler.target >= handler.end {
    //         arrows.push(Arrow {
    //             from: handler.start,
    //             to,
    //             kind,
    //         });
    //     } else if handler.target < handler.start {
    //         arrows.push(Arrow {
    //             from: handler.end,
    //             to,
    //             kind,
    //         });
    //     } else {
    //         // Target within [start; end), incredibly cursed, need to split into two `try`s.
    //         // Alternatively, we could keep a single `try` and then jump to the handler from within
    //         // `catch`, but that gets quite messy. A naive set of two chained arrows produces
    //         // hypothetical code like:
    //         //
    //         //     try {
    //         //         a;
    //         //     handler:
    //         //         b;
    //         //     } catch {
    //         //         goto handler;
    //         //     }
    //         //
    //         // ...but we *can't* jump across blocks, which arrows would typically resolve, but not
    //         // here: the arrows only enabling jumping to the handler from *within* the `try` block,
    //         // and they don't know that `catch` is a neighbor of `try`, not a child. We could insert
    //         // a fake statement, e.g.:
    //         //
    //         //     a            |
    //         //     b            v ^
    //         //     fake           |
    //         //
    //         // and then those arrows would be extended via a dispatcher (see below) to:
    //         //
    //         //     dispatcher   | ^ |
    //         //     a            | | v
    //         //     b            v |
    //         //     fake           |
    //         //
    //         // which corresponds to code:
    //         //
    //         //     int selector = 0;
    //         //     while (true) {
    //         //         try {
    //         //             if (selector == 0) {
    //         //                 a;
    //         //             }
    //         //             b;
    //         //             break;
    //         //         } catch {
    //         //             selector = 1;
    //         //         }
    //         //     }
    //         //
    //         // which is more complicated and slower than the two-`try` version:
    //         //
    //         //     try {
    //         //         a;
    //         //     } catch {}
    //         //     while (true) {
    //         //         try {
    //         //             b;
    //         //             break;
    //         //         } catch {}
    //         //     }
    //         //
    //         // (The `catch {}` statements are deliberately left empty.)
    //         arrows.push(Arrow {
    //             from: handler.start,
    //             to,
    //             kind: kind.clone(),
    //         });
    //         arrows.push(Arrow {
    //             from: handler.end,
    //             to,
    //             kind,
    //         });
    //     }
    // }
}
