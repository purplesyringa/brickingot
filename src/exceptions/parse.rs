use super::{AnalysisBlockMeta, AnalysisIr, AnalysisMeta, Ir, Program};
use crate::ast::{
    Arena, BasicStatement, Catch, GroupId, Statement, StmtGroup, StmtMeta, isomorphism,
};
use crate::structured;
use rustc_hash::FxHashSet;

pub fn parse_try_blocks(arena: &Arena<'_>, ir: structured::Program) -> Program {
    // Our plan:
    // - Inline tails into `catch`.
    // - Recognize every `catch (...)` that looks like `finally`.
    // - Find patterns that exactly match such `finally`s inside `try` bodies.

    // Exits from `try` occur either on `return`, or on `break`/`continue` to a block outside `try`.
    // `finally` statements directly precede this statement.

    let mut analyzer = Analyzer {
        groups_with_breaks: FxHashSet::default(),
    };
    let ir = analyzer.handle_group(ir).0;

    let transformer = Transformer { arena };
    transformer.handle_group(ir, &mut Vec::new(), &mut Vec::new())
}

struct Analyzer {
    groups_with_breaks: FxHashSet<GroupId>,
}

impl Analyzer {
    fn handle_group(
        &mut self,
        group: StmtGroup<structured::Ir>,
    ) -> (StmtGroup<AnalysisIr>, AnalysisMeta) {
        let mut meta = AnalysisMeta {
            measure: 1,
            is_divergent: false,
        };
        let children = group
            .children
            .into_iter()
            .map(|stmt| self.handle_stmt(stmt))
            .inspect(|stmt_meta| {
                meta.measure += stmt_meta.meta.measure;
                meta.is_divergent = stmt_meta.meta.is_divergent;
            })
            .collect();
        (
            StmtGroup {
                id: group.id,
                children,
            },
            meta,
        )
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

            Statement::Block { body, .. } => {
                let (body, mut meta) = self.handle_group(body);
                let has_break = self.groups_with_breaks.remove(&body.id);
                meta.is_divergent &= !has_break;
                StmtMeta {
                    stmt: Statement::Block {
                        body,
                        meta: AnalysisBlockMeta { has_break },
                    },
                    meta,
                }
            }

            Statement::Continue { group_id, .. } => StmtMeta {
                stmt: Statement::continue_(group_id),
                meta: AnalysisMeta {
                    measure: 1,
                    is_divergent: true,
                },
            },

            Statement::Break { group_id, .. } => {
                self.groups_with_breaks.insert(group_id);
                StmtMeta {
                    stmt: Statement::break_(group_id),
                    meta: AnalysisMeta {
                        measure: 1,
                        is_divergent: true,
                    },
                }
            }

            Statement::If {
                condition,
                then,
                else_,
                ..
            } => {
                let (then, mut meta) = self.handle_group(then);
                assert!(
                    else_.children.is_empty(),
                    "shouldn't have anything in else yet",
                );
                let else_ = StmtGroup {
                    id: else_.id,
                    children: Vec::new(),
                };
                meta.is_divergent = false; // `else` is empty
                StmtMeta {
                    stmt: Statement::if_(condition, then, else_),
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
                    .map(|(value, body)| {
                        let (arm_body, arm_meta) = self.handle_group(body);
                        meta.measure += arm_meta.measure;
                        meta.is_divergent = arm_meta.is_divergent;
                        (value, arm_body)
                    })
                    .collect();
                let has_break = self.groups_with_breaks.remove(&id);
                meta.is_divergent &= !has_break;
                StmtMeta {
                    stmt: Statement::switch(id, key, arms),
                    meta,
                }
            }

            Statement::Try {
                try_,
                catches,
                finally,
                ..
            } => {
                let mut meta = AnalysisMeta {
                    measure: 1,
                    is_divergent: false,
                };

                let (try_, try_meta) = self.handle_group(try_);
                meta.measure += try_meta.measure;
                meta.is_divergent = try_meta.is_divergent;

                let catches = catches
                    .into_iter()
                    .map(|catch| {
                        let (catch_body, catch_meta) = self.handle_group(catch.body);
                        meta.measure += catch_meta.measure;
                        meta.is_divergent &= catch_meta.is_divergent;
                        Catch {
                            class: catch.class,
                            value_var: catch.value_var,
                            body: catch_body,
                            meta: catch.meta,
                        }
                    })
                    .collect();

                assert!(
                    finally.children.is_empty(),
                    "shouldn't have anything in finally yet",
                );
                let finally = StmtGroup {
                    id: finally.id,
                    children: Vec::new(),
                };

                StmtMeta {
                    stmt: Statement::try_(try_, catches, finally),
                    meta,
                }
            }
        }
    }
}

// A list of iterators over statements that are known to be executed by fallthrough after the
// current statement, and *only* by that fallthrough. The statements always directly follow the
// current statement without skipping any statements, but may cross `} #n` boundaries as long the
// group is never broken from.
type Tail = Vec<alloc::vec::IntoIter<StmtMeta<AnalysisIr>>>;

// A list of open `try` blocks with non-empty `finally` bodies.
type Finalizers = Vec<Finalizer>;
struct Finalizer {
    try_id: GroupId,
    body: Vec<StmtMeta<AnalysisIr>>,
}

struct Transformer<'arena, 'code> {
    arena: &'arena Arena<'code>,
}

impl Transformer<'_, '_> {
    fn handle_group(
        &self,
        mut group: StmtGroup<AnalysisIr>,
        tail: &mut Tail,
        finalizers: &mut Finalizers,
    ) -> StmtGroup<Ir> {
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
        let last_stmt = group.children.last().map(|stmt_meta| &stmt_meta.stmt);
        let exits_group_id = match last_stmt {
            Some(Statement::Basic {
                stmt: BasicStatement::Return { .. } | BasicStatement::ReturnVoid,
                ..
            }) => Some(GroupId::ROOT),
            Some(Statement::Continue { group_id, .. } | Statement::Break { group_id, .. }) => {
                Some(*group_id)
            }
            _ => None,
        };
        if let Some(exits_group_id) = exits_group_id {
            let start = finalizers.partition_point(|finalizer| finalizer.try_id < exits_group_id);

            // Try to match finalizers. If an expected finalizer could not be matched, it's not
            // a big deal: we can use what Vineflower calls "predicated finally block", i.e. wrap
            // the `finally` contents in an `if` whose condition is set on "good" exits and reset on
            // "bad" exits from `try` body.
            //
            // If there are multiple expected finalizers, we find the longest matching suffix (i.e.
            // resolve as many `try`s from outside in as possible). In principle, this is not the
            // only valid approach: this is similar to a knapsack problem, and we could also use
            // a greedy solution or look for an optimal one. Neither option is intuitive, and
            // neither can really be implemented efficiently, so matching the suffix is probably the
            // best idea.
            let mut i = group.children.len() - 1;
            for finalizer in &finalizers[start..] {
                if self.compare_stmt_lists(
                    &group.children[i.saturating_sub(finalizer.body.len())..i],
                    &finalizer.body,
                ) {
                    i -= finalizer.body.len();
                } else {
                    break;
                }
            }
            group.children.drain(i..group.children.len() - 1);
        }

        // Map the statements and inline into `catch`es present within `group.children`.
        let mut children = Vec::with_capacity(group.children.len());
        let mut it = group.children.into_iter();
        while let Some(stmt) = it.next() {
            tail.push(it);
            children.push(self.handle_stmt(stmt, tail, finalizers));
            it = tail.pop().unwrap();
        }
        StmtGroup {
            id: group.id,
            children,
        }
    }

    fn handle_stmt(
        &self,
        stmt_meta: StmtMeta<AnalysisIr>,
        tail: &mut Tail,
        finalizers: &mut Finalizers,
    ) -> Statement<Ir> {
        match stmt_meta.stmt {
            Statement::Basic { stmt, .. } => Statement::basic(stmt),

            Statement::Block { body, meta } => {
                let mut empty_tail = Vec::new();
                Statement::block(self.handle_group(
                    body,
                    if meta.has_break {
                        &mut empty_tail
                    } else {
                        tail
                    },
                    finalizers,
                ))
            }

            Statement::Continue { group_id, .. } => Statement::continue_(group_id),

            Statement::Break { group_id, .. } => Statement::break_(group_id),

            Statement::If {
                condition,
                then,
                else_,
                ..
            } => Statement::if_(
                condition,
                self.handle_group(then, &mut Vec::new(), finalizers),
                StmtGroup {
                    id: else_.id,
                    children: Vec::new(),
                },
            ),

            Statement::Switch { id, key, arms, .. } => {
                let arms = arms
                    .into_iter()
                    .map(|(value, body)| {
                        // Strictly speaking, the tail might not be empty for the last arm, but we
                        // never generate `try` inside `switch` cases on the previous passes so it
                        // doesn't matter.
                        (value, self.handle_group(body, &mut Vec::new(), finalizers))
                    })
                    .collect();
                Statement::switch(id, key, arms)
            }

            Statement::Try {
                try_,
                mut catches,
                finally,
                ..
            } => {
                assert_eq!(catches.len(), 1, "must have a single catch");
                let mut catch = catches.pop().unwrap();

                let try_body_is_divergent = try_
                    .children
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
                    for list in tail.iter_mut().rev() {
                        catch.body.children.extend(list);
                        // XXX: this can invalidate `catch.meta`, oh no, what do I do??? -- stupid ass bitch
                    }
                }

                finalizers.push(Finalizer {
                    try_id: try_.id,
                    body: Vec::new(), // FIXME
                });
                let try_ = self.handle_group(try_, &mut Vec::new(), finalizers);
                finalizers.pop();

                let catch_body = self.handle_group(catch.body, &mut Vec::new(), finalizers);

                let finally = StmtGroup {
                    id: finally.id,
                    children: Vec::new(),
                };

                Statement::try_(
                    try_,
                    vec![Catch {
                        class: catch.class,
                        value_var: catch.value_var,
                        body: catch_body,
                        meta: catch.meta,
                    }],
                    finally,
                )
            }
        }
    }

    fn compare_stmt_lists(&self, xs: &[StmtMeta<AnalysisIr>], ys: &[StmtMeta<AnalysisIr>]) -> bool {
        // The implementation details of this isomorphism check significantly affect the time
        // complexity guarantees of the EH pass. The guarantee sufficient for overall linear time
        // is: if we decide to recurse into `xs`, we never recurse into subtrees of `xs`.
        isomorphism::compare(self.arena, xs, ys)
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
