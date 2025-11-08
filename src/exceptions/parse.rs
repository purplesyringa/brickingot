use super::{AnalysisBlockMeta, AnalysisIr, AnalysisMeta, Ir, Program};
use crate::ast::{BasicStatement, Catch, Statement, StmtList, StmtMeta};
use crate::structured;
use core::cell::Cell;
use rustc_hash::FxHashSet;

pub fn parse_try_blocks(ir: structured::Program) -> Program {
    // Our plan:
    // - Inline tails into `catch`.
    // - Recognize every `catch (...)` that looks like `finally`.

    // Exits from `try` occur either on `return`, or on `break`/`continue` to a block outside `try`.
    // `finally` statements directly precede this statement.

    let mut analyzer = Analyzer {
        blocks_with_breaks: FxHashSet::default(),
    };
    let ir = analyzer.handle_stmt_list(ir).0;

    Transformer.handle_stmt_list(ir, None, None, 0)
}

struct Analyzer {
    blocks_with_breaks: FxHashSet<usize>,
}

impl Analyzer {
    fn handle_stmt_list(
        &mut self,
        stmts: StmtList<structured::Ir>,
    ) -> (StmtList<AnalysisIr>, AnalysisMeta) {
        let mut meta = AnalysisMeta {
            measure: 1,
            is_divergent: false,
        };
        let out = stmts
            .into_iter()
            .map(|stmt| self.handle_stmt(stmt))
            .inspect(|stmt_meta| {
                meta.measure += stmt_meta.meta.measure;
                meta.is_divergent = stmt_meta.meta.is_divergent;
            })
            .collect();
        (out, meta)
    }

    fn handle_stmt(&mut self, stmt: Statement<structured::Ir>) -> StmtMeta<AnalysisIr> {
        match stmt {
            Statement::Basic { stmt, .. } => {
                let meta = AnalysisMeta {
                    measure: 1,
                    is_divergent: stmt.is_divergent(),
                };
                StmtMeta {
                    stmt: Statement::basic(stmt),
                    meta,
                }
            }

            Statement::Block { id, children, .. } => {
                let (children, mut meta) = self.handle_stmt_list(children);
                let has_break = self.blocks_with_breaks.remove(&id);
                meta.is_divergent &= !has_break;
                StmtMeta {
                    stmt: Statement::Block {
                        id,
                        children,
                        meta: AnalysisBlockMeta { has_break },
                    },
                    meta,
                }
            }

            Statement::Continue { block_id, .. } => StmtMeta {
                stmt: Statement::continue_(block_id),
                meta: AnalysisMeta {
                    measure: 1,
                    is_divergent: true,
                },
            },

            Statement::Break { block_id, .. } => {
                self.blocks_with_breaks.insert(block_id);
                StmtMeta {
                    stmt: Statement::break_(block_id),
                    meta: AnalysisMeta {
                        measure: 1,
                        is_divergent: true,
                    },
                }
            }

            Statement::If {
                condition,
                then_children,
                else_children,
                ..
            } => {
                let (then_children, mut meta) = self.handle_stmt_list(then_children);
                assert!(
                    else_children.is_empty(),
                    "shouldn't have anything in else yet",
                );
                meta.is_divergent = false; // `else` is empty
                StmtMeta {
                    stmt: Statement::if_(condition, then_children, Vec::new()),
                    meta,
                }
            }

            Statement::Switch { id, key, arms, .. } => {
                let mut meta = AnalysisMeta {
                    measure: 1,
                    is_divergent: false,
                };
                let arms = arms
                    .into_iter()
                    .map(|(value, children)| {
                        let (arm_stmts, arm_meta) = self.handle_stmt_list(children);
                        meta.measure += arm_meta.measure;
                        meta.is_divergent = arm_meta.is_divergent;
                        (value, arm_stmts)
                    })
                    .collect();
                let has_break = self.blocks_with_breaks.remove(&id);
                meta.is_divergent &= !has_break;
                StmtMeta {
                    stmt: Statement::switch(id, key, arms),
                    meta,
                }
            }

            Statement::Try {
                try_children,
                catches,
                ..
            } => {
                let mut meta = AnalysisMeta {
                    measure: 1,
                    is_divergent: false,
                };

                let (try_children, try_meta) = self.handle_stmt_list(try_children);
                meta.measure += try_meta.measure;
                meta.is_divergent = try_meta.is_divergent;

                let catches = catches
                    .into_iter()
                    .map(|catch| {
                        let (catch_stmts, catch_meta) = self.handle_stmt_list(catch.children);
                        meta.measure += catch_meta.measure;
                        meta.is_divergent &= catch_meta.is_divergent;
                        Catch {
                            class: catch.class,
                            children: catch_stmts,
                            meta: catch.meta,
                        }
                    })
                    .collect();

                StmtMeta {
                    stmt: Statement::try_(try_children, catches, Vec::new()),
                    meta,
                }
            }
        }
    }
}

struct Transformer;

// A linked list with stack-allocated nodes. This is admittedly a weird data structure, but we can't
// use vectors without `unsafe` here if we want `T` to contain references to locals.
type LinkedList<'a, T> = Option<&'a LinkedListNode<'a, T>>;
struct LinkedListNode<'a, T> {
    value: T,
    next: LinkedList<'a, T>,
}

// A list of iterators over statements that are known to be executed by fallthrough after the
// current statement, and *only* by that fallthrough. The statements always directly follow the
// current statement without skipping any statements, but may cross `} block #n` boundaries as long
// the block is never broken from.
type Tail<'a> = LinkedList<'a, TailNode<'a>>;
struct TailNode<'a> {
    // Logically `&mut`, but covariance forces using `&Cell`.
    list: &'a Cell<alloc::vec::IntoIter<StmtMeta<AnalysisIr>>>,
}

// A list of open `try` blocks with finalizers.
type Finalizers<'a> = LinkedList<'a, Finalizer<'a>>;
struct Finalizer<'a> {
    nested_in_block_id: usize,
    body: &'a [StmtMeta<Ir>],
}

impl Transformer {
    fn handle_stmt_list(
        &self,
        stmts: StmtList<AnalysisIr>,
        tail: Tail<'_>,
        finalizers: Finalizers<'_>,
        nested_in_block_id: usize,
    ) -> StmtList<Ir> {
        // Scan for anything that looks similar to a finalizer.
        //
        // This should be done before we recurse into `stmts`, so that we compare unprocessed
        // finalizers within `try` to the unprocessed finalizer in `finally`. Swapping the order
        // would lead to comparing apples to oranges: not only would the typing be weird, it could
        // also break isomorphism because `catch` contents could be inlined in the haystack, but not
        // in the needle, or vice versa.
        //
        // In addition, comparing pre-inlining finalizers is much simpler than comparing
        // post-inlining finalizers, since a pre-inlining finalizer is guaranteed to be directly
        // followed by a `break`/`continue`/`return`, whereas for a post-inlining finalizer it might
        // be located deep within the last statement.

        for (i, stmt_meta) in stmts.iter().enumerate() {
            let block_id = match stmt_meta.stmt {
                Statement::Basic {
                    stmt: BasicStatement::Return { .. } | BasicStatement::ReturnVoid,
                    ..
                } => 0,
                Statement::Continue { block_id, .. } | Statement::Break { block_id, .. } => {
                    block_id
                }
                _ => continue,
            };
            // Quitting to `block_id` -- expect to run finalizers from each exitted `try` block.
        }

        // Map the statements and inline into `catch`es present within `stmts`.
        let mut out = Vec::with_capacity(stmts.len());
        let mut it = stmts.into_iter();
        while let Some(stmt) = it.next() {
            out.push(self.handle_stmt(
                stmt,
                Some(&LinkedListNode {
                    value: TailNode {
                        list: Cell::from_mut(&mut it),
                    },
                    next: tail,
                }),
                finalizers,
                nested_in_block_id,
            ));
        }
        out
    }

    fn handle_stmt(
        &self,
        stmt_meta: StmtMeta<AnalysisIr>,
        tail: Tail<'_>,
        finalizers: Finalizers<'_>,
        nested_in_block_id: usize,
    ) -> Statement<Ir> {
        match stmt_meta.stmt {
            Statement::Basic { stmt, .. } => Statement::basic(stmt),

            Statement::Block { id, children, meta } => Statement::block(
                id,
                self.handle_stmt_list(
                    children,
                    if meta.has_break { None } else { tail },
                    finalizers,
                    id,
                ),
            ),

            Statement::Continue { block_id, .. } => Statement::continue_(block_id),

            Statement::Break { block_id, .. } => Statement::break_(block_id),

            Statement::If {
                condition,
                then_children,
                ..
            } => Statement::if_(
                condition,
                self.handle_stmt_list(then_children, None, finalizers, nested_in_block_id),
                Vec::new(),
            ),

            Statement::Switch { id, key, arms, .. } => {
                let arms = arms
                    .into_iter()
                    .map(|(value, children)| {
                        // Strictly speaking, it might not be `None` for the last arm, but we never
                        // generate `try` inside `switch` cases on the previous passes so it doesn't
                        // matter.
                        (value, self.handle_stmt_list(children, None, finalizers, id))
                    })
                    .collect();
                Statement::switch(id, key, arms)
            }

            Statement::Try {
                try_children,
                mut catches,
                ..
            } => {
                assert_eq!(catches.len(), 1, "must have a single catch");
                let mut catch = catches.pop().unwrap();

                let try_body_is_divergent = try_children
                    .last()
                    .is_some_and(|stmt_meta| stmt_meta.meta.is_divergent);
                if try_body_is_divergent {
                    // Inline tail. This can inline more than just the `catch` body, since it can
                    // also inline e.g. the iteration statement of a `for` loop.
                    //
                    // This is somewhat confusing, but ultimately does not break any invariant. We
                    // need every block to either have a `break` to it or to end with something
                    // containing a `continue` to it, but we're inlining into `catch`, not into
                    // a block. The loop decoder is prepared to deal with this mess, since it has to
                    // deal with overinlining into an `if`'s `else` branch anyway.
                    let mut it = tail;
                    while let Some(&LinkedListNode {
                        value: TailNode { list },
                        next,
                    }) = it
                    {
                        catch.children.extend(list.take().into_iter().rev());
                        // XXX: this can invalidate `catch.meta`, oh no, what do I do??? -- stupid ass bitch
                        it = next;
                    }
                }

                let try_children = self.handle_stmt_list(
                    try_children,
                    None,
                    Some(&LinkedListNode {
                        value: Finalizer {
                            nested_in_block_id,
                            body: &[], // FIXME
                        },
                        next: finalizers,
                    }),
                    nested_in_block_id,
                );

                let catch_children =
                    self.handle_stmt_list(catch.children, None, finalizers, nested_in_block_id);

                Statement::try_(
                    try_children,
                    vec![Catch {
                        class: catch.class,
                        children: catch_children,
                        meta: catch.meta,
                    }],
                    Vec::new(),
                )
            }
        }
    }
}

// // `try` blocks are not guaranteed to be nested correctly. Even if nested, the outer `try` block can
// // have more priority than the inner one.
// //
// // There's no better way to handle this than forcing the inner `try` block to be as large as the
// // outer one. But that would require not just its left end, but also its right end to be extended,
// // which would change the position of `catch` and force us to insert a backward jump. We thus need
// // to perform these extensions before the requirement list is generated. That's what
// // `treeify_try_blocks` does.
// //
// // We need to make sure that syntactic extension of the `try` range does not affect semantics, which
// // we do by creating a synthetic variable that effectively tracks the program counter. We could do
// // it slightly differently by creating a per-`try`-block synthetic `bool` variable that tracks EH
// // eligibility, but that would be superlinear in the worst case. Since incorrectly nested `try`
// // blocks should only occur in obfuscated code, it's likely that this worst case would in fact be
// // reached in practice, so a single variable will hopefully be simpler not just for us, but for the
// // end user as well.

// use super::{ExceptionHandler, Program, Statement};
// use crate::ast::{
//     Arena, BasicStatement, BinOp, Expression, LogicalOp, Variable, VariableName, VariableNamespace,
// };
// use alloc::collections::BTreeMap;
// use core::cmp::Reverse;
// use core::ops::Range;

// #[derive(Clone)]
// struct ExtendedHandler {
//     handler_id: usize,
//     active_range: Range<usize>,
// }

// pub fn legalize_exception_handling<'code>(arena: &mut Arena<'code>, program: &mut Program<'code>) {
//     let extended_handlers = treeify_try_blocks(&mut program.exception_handlers);
//     if extended_handlers.is_empty() {
//         return;
//     }

//     let (context_ids, handler_context_ids) = compute_contexts(
//         program.basic_blocks.len(),
//         &extended_handlers
//             .iter()
//             .map(|handler| handler.active_range.clone())
//             .collect::<Vec<_>>(),
//     );

//     // This allocates a single version for the context variables, which is not exactly optimal, but
//     // more than fine for readability.
//     let context_version = arena.alloc(Expression::Null);
//     let context_var = var!(context0 v context_version);

//     // Add context checks to exception handlers.
//     for (handler, context_id_range) in extended_handlers.into_iter().zip(handler_context_ids) {
//         let condition = if context_id_range.len() == 1 {
//             arena.alloc(Expression::BinOp {
//                 op: BinOp::Eq,
//                 lhs: arena.var(context_var),
//                 rhs: arena.int(context_id_range.start as i32),
//             })
//         } else {
//             arena.alloc(Expression::LogicalOp {
//                 op: LogicalOp::And,
//                 lhs: arena.alloc(Expression::BinOp {
//                     op: BinOp::Ge,
//                     lhs: arena.var(context_var),
//                     rhs: arena.int(context_id_range.start as i32),
//                 }),
//                 rhs: arena.alloc(Expression::BinOp {
//                     op: BinOp::Le,
//                     lhs: arena.var(context_var),
//                     rhs: arena.int(context_id_range.end as i32 - 1),
//                 }),
//             })
//         };

//         program.exception_handlers[handler.handler_id]
//             .body
//             .condition = Some(condition);
//     }

//     // Assign contexts.
//     //
//     // The invariant here is that, on entry to each basic block, the correct context ID is stored in
//     // the synthetic. This allows us to remove assignments in basic blocks whose predecessors all
//     // have the same context ID. This does not result in the *minimal* number of assignments, but
//     // that's not our goal -- we mostly want code to stay readable, and this seems more intuitive
//     // than solving a problem that is likely NP-hard.
//     for (bb_id, (bb, context_id)) in program
//         .basic_blocks
//         .iter_mut()
//         .zip(&context_ids)
//         .enumerate()
//     {
//         // Always assign at the entry to the function. This kind of acts as the base case of
//         // recursion.
//         if bb_id != 0
//             && bb
//                 .predecessors
//                 .iter()
//                 .all(|pred_bb_id| context_ids[*pred_bb_id] == *context_id)
//         {
//             continue;
//         }

//         bb.statements.insert(
//             0,
//             Statement::Basic(BasicStatement::Assign {
//                 target: context_var(),
//                 value: arena.int(*context_id as i32),
//             }),
//         )
//     }
// }
