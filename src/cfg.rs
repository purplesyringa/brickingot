use crate::arrows::{Arrow, ArrowKind, extend_arrows};
use crate::ast::{BasicStatement, BinOp, Expression, Str, VariableNamespace};
use crate::unstructured::{self, JumpCondition};
use core::cmp::Reverse;
use core::fmt::{self, Display};
use core::ops::Range;
use noak::MStr;
use std::collections::HashMap;

#[derive(Debug)]
pub enum Statement<'a> {
    Basic(BasicStatement<'a>),
    Block {
        id: usize,
        children: Vec<Statement<'a>>,
    },
    If {
        condition: Box<Expression<'a>>,
        then_children: Vec<Statement<'a>>,
        else_children: Vec<Statement<'a>>,
    },
    Switch {
        key: Box<Expression<'a>>,
        arms: Vec<(i32, Vec<Statement<'a>>)>,
    },
    JumpToBlockStart {
        block_id: usize,
    },
    JumpToBlockEnd {
        block_id: usize,
    },
    Try {
        children: Vec<Statement<'a>>,
        catches: Vec<Catch<'a>>,
    },
    TryRangeMarker {
        id: usize,
    },
}

#[derive(Debug)]
pub struct Catch<'a> {
    pub class: Option<Str<'a>>,
    pub children: Vec<Statement<'a>>,
    pub active_range: Range<usize>,
}

impl Statement<'_> {
    // This is just a helper function for building the AST. It's deliberately private and shouldn't
    // be used for AST modification after it's built.
    fn append_child(&mut self, child: Self) {
        match self {
            Self::Basic(_) => panic!("cannot append child to basic statement"),
            Self::Block { children, .. } => children.push(child),
            Self::If { .. } => panic!("cannot append child to If"),
            Self::Switch { .. } => panic!("cannot append child to Switch"),
            Self::JumpToBlockStart { .. } => panic!("cannot append child to JumpToBlockStart"),
            Self::JumpToBlockEnd { .. } => panic!("cannot append child to JumpToBlockEnd"),
            Self::Try { children, .. } => children.push(child),
            Self::TryRangeMarker { .. } => panic!("cannot append child to TryRangeMarker"),
        }
    }
}

impl Display for Statement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Basic(basic) => write!(f, "{basic}"),
            Self::Block { id, children } => {
                write!(f, "block #{id} {{\n")?;
                for child in children {
                    write!(f, "{child}\n")?;
                }
                write!(f, "}} block #{id}")
            }
            Self::If {
                condition,
                then_children,
                else_children,
            } => {
                write!(f, "if ({condition}) {{\n")?;
                for child in then_children {
                    write!(f, "{child}\n")?;
                }
                write!(f, "}} else {{\n")?;
                for child in else_children {
                    write!(f, "{child}\n")?;
                }
                write!(f, "}}")
            }
            Self::Switch { key, arms } => {
                write!(f, "switch ({key}) {{\n")?;
                for (value, children) in arms {
                    write!(f, "case {value}:\n")?;
                    for child in children {
                        write!(f, "{child}\n")?;
                    }
                }
                write!(f, "}}")
            }
            Self::JumpToBlockStart { block_id } => write!(f, "continue #{block_id};"),
            Self::JumpToBlockEnd { block_id } => write!(f, "break #{block_id};"),
            Self::Try { children, catches } => {
                write!(f, "try {{\n")?;
                for child in children {
                    write!(f, "{child}\n")?;
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
                        write!(f, "{child}\n")?;
                    }
                }
                write!(f, "}}")
            }
            Self::TryRangeMarker { id } => write!(f, "try marker #{id};"),
        }
    }
}

fn selector<'a>() -> Box<Expression<'a>> {
    Box::new(Expression::Variable {
        id: 0,
        namespace: VariableNamespace::Selector,
    })
}

pub fn structurize_cfg(mut program_in: unstructured::Program<'_>) -> Statement<'_> {
    // Arrows are ordered pairs `(x, y)`, written `x -> y` or `y <- x`, indicating "travelling"
    // between gaps. A gap is the space between two statements; the index of a gap is the index of
    // the statement immediately following it. The presence of an arrow `x -> y` indicates that
    // there needs to be a way to travel from any statement between gaps `x` and `y` (or `y` and
    // `x`) to the gap `y`. Travelling from gap `x` to gap `x + 1` is implicitly allowed.
    //
    // Our current goal is to collect the arrows, which succinctly represent a linearized CFG. We
    // will then apply certain transforms (mostly elongating tails and splitting arrows into two) to
    // ensure they form a tree (i.e. any two arrows are either nested or don't intersect), which
    // we'll then turn into an AST.

    let mut arrows = Vec::new();

    let mut add_branch = |mut from: usize, to: usize, inner_index: usize| {
        let kind = ArrowKind::Jump {
            stmt_index: from,
            inner_index,
        };
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
            unstructured::Statement::Jump { target, .. } => add_branch(index, *target, 0),
            unstructured::Statement::Switch(unstructured::Switch {
                successors,
                default,
                ..
            }) => {
                for (i, (_, successor)) in successors.iter().enumerate() {
                    add_branch(index, *successor, i + 1);
                }
                add_branch(index, *default, 0);
            }
        }
    }

    // Exception handlers also affect control flow: we need to be able to travel from any statement
    // within the `try` block to the exception handler. This is a little harder than it seems,
    // because adding the minimal arrow containing the guarded statements does not guarantee that we
    // can wrap the corresponding statements in a single `try` block.
    //
    // Consider, for example, the following input program:
    //
    //     print a;            \                                        |   : :
    //     if (...) goto 1;    | try { ... } catch { goto 2; }          | | : :
    //     print b;            /                                        | | : :
    //     goto 3;                                                      | v | :
    // 1:  print c;                                                     |   | :
    //     goto 3;                                                      v   | |
    // 2:  print d;                                                         v v
    // 3:
    //
    // ...which is a variant of the following snippet, just with messier control flow, namely
    // exceptions at `print c;` not being caught:
    //
    //     try {
    //         print a;
    //         if (!...) {
    //             print b;
    //         } else {
    //             print c;
    //         }
    //     } catch {
    //         print d;
    //     }
    //
    // A `try` block cannot be added around the first three statements because it would get
    // interleaved with the `goto 1` arrow. We can instead capture the six statements within the
    // range of the (extended) `try` arrow, which corresponds to the following decompilation:
    //
    //     boolean is_in_range = true;
    //     try {
    //         print a;
    //         if (!...) {
    //             print b;
    //         } else {
    //             is_in_range = false;
    //             print c;
    //         }
    //     } catch {
    //         if (!is_in_range) rethrow;
    //         print d;
    //     }
    //
    // There a seemingly simpler way to handle this that doesn't introduce synthetic variables. We
    // could wrap each statement in an individual `try..catch` block and then merge neighboring
    // `try` blocks together. However this inhibits certain rewrites that significantly simplify
    // the code in other ways. On the snippet above, such an approach would lead to the following
    // decompilation:
    //
    //     do {
    //         try {
    //             print a;
    //         } catch {
    //             break;
    //         }
    //         do {
    //             try {
    //                 if (...) {
    //                     break;
    //                 }
    //                 print b;
    //             } catch {
    //                 break 2;
    //             }
    //             return;
    //         } while (false);
    //         print c;
    //         return;
    //     } while (false);
    //     print d;
    //
    // We have to use `break`s in `catch` and add `do { ... } while (false);` to deduplicate the
    // exception handler, and even if we didn't care about that, `print c;` still needs to be
    // accessed via a `break;` so that it's outside the `try` block.
    //
    // Another nasty problem is the quadratic symptotic complexity of `try` block splitting. `try`
    // blocks are not guaranteed to nest correctly, and that means that even if two `try` blocks
    // are nested, the larger one can have priority over the smaller one, and that means that
    // the exception handling ranges like here:
    //
    //     a;   \
    //     b;   | \
    //     c;   | | \
    //     d;   | | | \
    //     e;   / / / / |
    //
    // ...would have to be compiled to:
    //
    //     try {
    //         a;
    //     } catch { 1 }
    //     try {
    //         try {
    //             b;
    //         } catch { 1 }
    //     } catch { 2 }
    //     try {
    //         try {
    //             try {
    //                 c;
    //             } catch { 1 }
    //         } catch { 2 }
    //     } catch { 3 }
    //     ...
    //
    // Meanwhile, the region tracking approach is linear: we can basically track the index of the
    // statement currently being evaluated by setting a synthetic variable prior to each statement,
    // and then check if the index is in range for the exception handler with an O(1)
    // `const <= synthetic-var < const` comparison. This approach has a runtime cost, but, frankly
    // speaking, HotSpot doesn't like complex constructs like this one anyway, so the goal here is
    // just to generate reasonable code.

    let mut exception_handling_boundaries = Vec::new();

    for (handler_index, handler) in program_in.exception_handlers.iter().enumerate() {
        exception_handling_boundaries.push(handler.start);
        exception_handling_boundaries.push(handler.end);

        let to = handler.target;
        let kind = ArrowKind::Try { handler_index };
        if handler.target >= handler.end {
            arrows.push(Arrow {
                from: handler.start,
                to,
                kind,
            });
        } else if handler.target < handler.start {
            arrows.push(Arrow {
                from: handler.end,
                to,
                kind,
            });
        } else {
            // Target within [start; end), incredibly cursed, need to split into two `try`s.
            // Alternatively, we could keep a single `try` and then jump to the handler from within
            // `catch`, but that gets quite messy. A naive set of two chained arrows produces
            // hypothetical code like:
            //
            //     try {
            //         a;
            //     handler:
            //         b;
            //     } catch {
            //         goto handler;
            //     }
            //
            // ...but we *can't* jump across blocks, which arrows would typically resolve, but not
            // here: the arrows only enabling jumping to the handler from *within* the `try` block,
            // and they don't know that `catch` is a neighbor of `try`, not a child. We could insert
            // a fake statement, e.g.:
            //
            //     a            |
            //     b            v ^
            //     fake           |
            //
            // and then those arrows would be extended via a dispatcher (see below) to:
            //
            //     dispatcher   | ^ |
            //     a            | | v
            //     b            v |
            //     fake           |
            //
            // which corresponds to code:
            //
            //     int selector = 0;
            //     while (true) {
            //         try {
            //             if (selector == 0) {
            //                 a;
            //             }
            //             b;
            //             break;
            //         } catch {
            //             selector = 1;
            //         }
            //     }
            //
            // which is more complicated and slower than the two-`try` version:
            //
            //     try {
            //         a;
            //     } catch {}
            //     while (true) {
            //         try {
            //             b;
            //             break;
            //         } catch {}
            //     }
            //
            // (The `catch {}` statements are deliberately left empty.)
            arrows.push(Arrow {
                from: handler.start,
                to,
                kind: kind.clone(),
            });
            arrows.push(Arrow {
                from: handler.end,
                to,
                kind,
            });
        }
    }

    exception_handling_boundaries.sort_by_key(|index| Reverse(*index));
    exception_handling_boundaries.dedup();

    // We now wish to extend arrows to turn the arrow set into a tree. The following paper forms the
    // basis for our algorithm -- feel free to read it, although we'll describe the main details
    // below:
    //
    //     Lyle Ramshaw. 1988. Eliminating go to's while preserving program structure.
    //     J. ACM 35, 4 (Oct. 1988), 893–920. https://doi.org/10.1145/48014.48021
    //
    // Our main goal is to get rid of conflicts, i.e. intersecting arrows. The intersecting parts of
    // the arrows can be either heads or tails independently, forming four categories of conflicts:
    // forward (both arrows pointed downward), backward (both pointer upward), tail-to-tail
    // (conflicting via tails), and head-to-head.
    //
    // The paper proves that all but head-to-head conflicts can be resolved by elongating arrow
    // tails. Such an operation only increases the set of allowed movements, and is thus lossless.
    //
    // Head-to-head conflicts, however, cannot be resolved by elongation, and it can be proven that
    // a "zero-cost" is impossible. We use a novel (or at least one that's not explicitly described
    // in literature) non-zero-cost solution instead: dispatchers. Conflicts are handled by
    // stretching the head of the backwards-pointing arrow to the tail of the forward arrow, and
    // then adding another forward arrow to return to the correct position. (In this diagram,
    // statements are oriented to the right rather than downwards for brevity.)
    //
    //     ----------------->              normal jump
    //               <--------------
    //
    //                  ||
    //                  vv
    //
    //     ----------------->              normal jump
    //     <------------------------       jump to dispatcher
    //     --------->                      dispatch
    //
    // Immediately before the statement the "jump to dispatcher" arrow points to, a *dispatcher* is
    // inserted. The dispatcher reads a synthetic local variable, called *selector*, and either
    // jumps to one of the arrow heads, or skips to the next statement depending on its value. The
    // selector is assigned at the end of each predecessor of the dispatcher.
    //
    // This is kind of like a state machine, but a local one. If one part of a large function
    // contains irreducible control flow, we don't rewrite the entier function to use a state
    // machine, we minimize the impact.
    extend_arrows(&mut arrows);

    // Arrows can be directly mapped onto structured control flow blocks. This does not immediately
    // produce a beautiful result, but we can prettify the code at a later stage, when an AST is
    // already built. This is a little inefficient, but the interaction with exceptions and the
    // sheer complexity of arrow-level rewrites required to parse common control flow structures
    // during this stage makes this task difficult to perform soundly. (I've tried.)

    let mut dispatchers: HashMap<usize, Vec<usize>> = HashMap::new();
    for arrow in &arrows {
        if arrow.kind == ArrowKind::Dispatch {
            dispatchers.entry(arrow.from).or_default().push(arrow.to);
        }
    }
    for (_, targets) in &mut dispatchers {
        targets.sort();
        targets.dedup();
    }

    arrows.sort_by_key(|arrow| (Reverse(arrow.from.min(arrow.to)), arrow.from.max(arrow.to)));

    let mut detached_roots = vec![(
        usize::MAX,
        Statement::Block {
            id: 0,
            children: Vec::new(),
        },
    )];
    let mut last_block_id = 0;

    let mut jump_to_impl = HashMap::new();
    let mut dispatch_to_block = HashMap::new();

    for index in 0..program_in.statements.len() {
        while let Some((_, root)) = detached_roots.pop_if(|(max, _)| *max == index) {
            detached_roots.last_mut().unwrap().1.append_child(root);
        }

        dispatch_to_block.clear();

        while let Some(arrow) = arrows.pop_if(|arrow| arrow.from.min(arrow.to) == index) {
            let max = arrow.from.max(arrow.to);

            let structured_stmt = match arrow.kind {
                // A jumping arrow can be translated as `while (true) { ... break; }`, where jumping
                // up is a `continue;` and jumping down is a `break;`. In the AST, we denote this as
                // a simpler `block { ... }` type.
                ArrowKind::Jump {
                    stmt_index,
                    inner_index,
                } => {
                    let is_down = arrow.to > arrow.from;

                    let mut jump_impl = Vec::new();

                    if !is_down {
                        let target = match program_in.statements[stmt_index] {
                            unstructured::Statement::Jump { target, .. } => target,
                            _ => todo!(),
                        };
                        if arrow.to != target {
                            let selector_value = dispatchers[&arrow.to]
                                .binary_search(&target)
                                .expect("dispatcher missing")
                                as i32;
                            jump_impl.push(Statement::Basic(BasicStatement::Assign {
                                target: selector(),
                                value: Box::new(Expression::ConstInt(selector_value)),
                            }));
                        }
                    }

                    last_block_id += 1;
                    if is_down {
                        jump_impl.push(Statement::JumpToBlockEnd {
                            block_id: last_block_id,
                        });
                    } else {
                        jump_impl.push(Statement::JumpToBlockStart {
                            block_id: last_block_id,
                        });
                    }
                    jump_to_impl.insert((stmt_index, inner_index), jump_impl);

                    Statement::Block {
                        id: last_block_id,
                        children: Vec::new(),
                    }
                }

                // A trying arrow can be translated as `try { ... } catch { goto handler; }`, where
                // `goto handler;` is resolved in a trivial way. As the trying arrow may extend
                // beyond the exception handling boundaries, we attach metadata to the `catch` block
                // to denote the active range. This will be lowered to a synthetic variable test
                // later on, after certain AST optimizations.
                ArrowKind::Try { handler_index } => {
                    let handler = &program_in.exception_handlers[handler_index];
                    let active_range = handler.start..handler.end;
                    if arrow.to > arrow.from {
                        // The heads of downward arrows can never be moved.
                        Statement::Try {
                            children: Vec::new(),
                            catches: vec![Catch {
                                class: handler.class,
                                children: Vec::new(),
                                active_range,
                            }],
                        }
                    } else {
                        last_block_id += 1;
                        Statement::Block {
                            id: last_block_id,
                            children: vec![Statement::Try {
                                children: Vec::new(),
                                catches: vec![Catch {
                                    class: handler.class,
                                    children: vec![Statement::JumpToBlockStart {
                                        block_id: last_block_id,
                                    }],
                                    active_range,
                                }],
                            }],
                        }
                    }
                }

                // If dispatching is necessary, a synthetic variable is created, shared among
                // dispatchers, and `switch`es over this variable are inserted at each dispatch
                // location; jumps to a dispatcher set the selector.
                ArrowKind::Dispatch => {
                    last_block_id += 1;
                    dispatch_to_block.insert(arrow.to, last_block_id);
                    Statement::Block {
                        id: last_block_id,
                        children: Vec::new(),
                    }
                }
            };

            detached_roots.push((max, structured_stmt));
        }

        let root = &mut detached_roots.last_mut().unwrap().1;

        if exception_handling_boundaries
            .pop_if(|gap| *gap == index)
            .is_some()
        {
            root.append_child(Statement::TryRangeMarker { id: index });
        }

        if let Some(successors) = dispatchers.get(&index) {
            root.append_child(Statement::Switch {
                key: selector(),
                arms: successors
                    .iter()
                    .enumerate()
                    .map(|(selector_value, successor)| {
                        (
                            selector_value as i32,
                            vec![
                                Statement::Basic(BasicStatement::Assign {
                                    target: selector(),
                                    value: Box::new(Expression::ConstInt(-1)),
                                }),
                                Statement::JumpToBlockEnd {
                                    block_id: dispatch_to_block[successor],
                                },
                            ],
                        )
                    })
                    .collect(),
            });
        }

        // We need to take out the statement, which means we have to replace it with some garbage.
        // We can't iterate over `statements` to get owned `stmts` immediately because we need
        // random access to `statements` while handling arrows.
        let stmt = core::mem::replace(
            &mut program_in.statements[index],
            unstructured::Statement::Basic(BasicStatement::ReturnVoid),
        );

        match stmt {
            unstructured::Statement::Basic(stmt) => root.append_child(Statement::Basic(stmt)),

            unstructured::Statement::Jump { condition, .. } => {
                let jump_impl = jump_to_impl
                    .remove(&(index, 0))
                    .expect("missing jump arrow");

                // In a normal situation,
                //     if (cond) {
                //         // then body
                //     } else {
                //         // else body
                //     }
                // is compiled to
                //     if (!cond) goto else_body;
                //     // then body
                //     goto endif;
                //     else_body: // else body
                //     endif:
                // meaning that the condition needs to be inverted during decompilation. Note that
                // jump conditions only apply to integers and references, so this rewrite doesn't
                // have to consider floating-point numbers.
                let (lhs, rhs, op) = match condition {
                    JumpCondition::Always => {
                        for stmt in jump_impl {
                            root.append_child(stmt);
                        }
                        continue;
                    }
                    JumpCondition::Eq(a, b) => (a, b, BinOp::Ne),
                    JumpCondition::Ne(a, b) => (a, b, BinOp::Eq),
                    JumpCondition::Ge(a, b) => (a, b, BinOp::Lt),
                    JumpCondition::Gt(a, b) => (a, b, BinOp::Le),
                    JumpCondition::Le(a, b) => (a, b, BinOp::Gt),
                    JumpCondition::Lt(a, b) => (a, b, BinOp::Ge),
                };

                root.append_child(Statement::If {
                    condition: Box::new(Expression::BinOp { lhs, rhs, op }),
                    then_children: Vec::new(),
                    else_children: jump_impl,
                });
            }

            unstructured::Statement::Switch(switch) => todo!(),
        };
    }

    while detached_roots.len() > 1 {
        let (_, root) = detached_roots.pop().unwrap();
        detached_roots.last_mut().unwrap().1.append_child(root);
    }
    let mut root = detached_roots.pop().unwrap().1;

    if !exception_handling_boundaries.is_empty() {
        root.append_child(Statement::TryRangeMarker {
            id: program_in.statements.len(),
        });
    }

    root
}
