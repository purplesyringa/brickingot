use super::{AnalysisBlockMeta, AnalysisIr, AnalysisMeta, Ir, Program};
use crate::ast::{
    Arena, BasicStatement, Catch, ExprId, Expression, GroupId, Statement, StmtGroup, StmtList,
    StmtMeta, Variable, VariableNamespace, Version, isomorphism,
};
use crate::structured;
use core::ops::Range;
use rustc_hash::{FxHashMap, FxHashSet};

pub fn parse_try_blocks(arena: &Arena<'_>, ir: structured::Program) -> Program {
    // Our plan:
    // - Inline tails into `catch`.
    // - Recognize every `catch (...)` that looks like `finally`.
    // - Find patterns that exactly match such `finally`s inside `try` bodies.

    let mut analyzer = Analyzer {
        arena,
        groups_with_breaks: FxHashSet::default(),
        next_access_id: 0,
        var_info: FxHashMap::default(),
    };
    let ir = analyzer.handle_group(ir).0;

    let transformer = Transformer {
        arena,
        var_info: analyzer.var_info,
    };
    transformer.handle_group(ir, &mut Vec::new(), &mut Vec::new())
}

struct VariableInfo {
    use_range: Range<usize>,
    use_count: usize,
}

struct Analyzer<'arena, 'code> {
    arena: &'arena Arena<'code>,
    groups_with_breaks: FxHashSet<GroupId>,
    next_access_id: usize,
    var_info: FxHashMap<Version, VariableInfo>,
}

impl Analyzer<'_, '_> {
    fn handle_group(
        &mut self,
        group: StmtGroup<structured::Ir>,
    ) -> (StmtGroup<AnalysisIr>, AnalysisMeta) {
        let mut meta = AnalysisMeta {
            measure: 1,
            access_range: self.next_access_id..0,
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
        meta.access_range.end = self.next_access_id;
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
                let mut meta = AnalysisMeta {
                    measure: 1,
                    access_range: self.next_access_id..0,
                    is_divergent: stmt.is_divergent(),
                };
                for expr in stmt.subexprs() {
                    self.handle_expr(expr);
                }
                meta.access_range.end = self.next_access_id;
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
                    access_range: self.next_access_id..self.next_access_id,
                    is_divergent: true,
                },
            },

            Statement::Break { group_id, .. } => {
                self.groups_with_breaks.insert(group_id);
                StmtMeta {
                    stmt: Statement::break_(group_id),
                    meta: AnalysisMeta {
                        measure: 1,
                        access_range: self.next_access_id..self.next_access_id,
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
                let mut access_range = self.next_access_id..0;
                self.handle_expr(condition);
                access_range.end = self.next_access_id;
                let (then, then_meta) = self.handle_group(then);
                assert!(
                    else_.children.is_empty(),
                    "shouldn't have anything in else yet",
                );
                let else_ = StmtGroup {
                    id: else_.id,
                    children: Vec::new(),
                };
                StmtMeta {
                    stmt: Statement::if_(condition, then, else_),
                    meta: AnalysisMeta {
                        measure: then_meta.measure,
                        access_range,
                        is_divergent: false, // `else` is empty
                    },
                }
            }

            Statement::Switch { id, key, arms, .. } => {
                let mut meta = AnalysisMeta {
                    measure: 1,
                    access_range: self.next_access_id..0,
                    is_divergent: false,
                };
                self.handle_expr(key);
                let arms = arms
                    .into_iter()
                    .map(|(value, body)| {
                        let (arm_body, arm_meta) = self.handle_group(body);
                        meta.measure += arm_meta.measure;
                        meta.is_divergent = arm_meta.is_divergent;
                        (value, arm_body)
                    })
                    .collect();
                meta.access_range.end = self.next_access_id;
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
                    access_range: self.next_access_id..0,
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
                        self.handle_var(catch.value_var);
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

                meta.access_range.end = self.next_access_id;

                StmtMeta {
                    stmt: Statement::try_(try_, catches, finally),
                    meta,
                }
            }
        }
    }

    fn handle_expr(&mut self, expr_id: ExprId) {
        if let Expression::Variable(var) = self.arena[expr_id] {
            self.handle_var(var);
        }
        for sub_expr_id in self.arena[expr_id].subexprs() {
            self.handle_expr(sub_expr_id);
        }
    }

    fn handle_var(&mut self, var: Variable) {
        let var_info = self.var_info.entry(var.version).or_insert(VariableInfo {
            use_range: self.next_access_id..0,
            use_count: 0,
        });
        var_info.use_range.end = self.next_access_id + 1;
        self.next_access_id += 1;
        var_info.use_count += 1;
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
    body: StmtList<AnalysisIr>,
    measure: usize,
    access_range: Range<usize>,
}

impl Finalizer {
    fn compare(
        &self,
        arena: &Arena<'_>,
        var_info: &FxHashMap<Version, VariableInfo>,
        body: &[StmtMeta<AnalysisIr>],
    ) -> bool {
        let body_measure = body.iter().map(|stmt_meta| stmt_meta.meta.measure).sum();
        // Comparing the measure is necessary to guarantee overall linear time, see the comment in
        // `handle_group` below.
        self.measure == body_measure
            && isomorphism::compare(arena, &*self.body, body, |var| {
                let use_range = &var_info
                    .get(&var.version)
                    .expect("missing variable info")
                    .use_range;
                self.access_range.start <= use_range.start && use_range.end <= self.access_range.end
            })
    }
}

struct Transformer<'arena, 'code> {
    arena: &'arena Arena<'code>,
    var_info: FxHashMap<Version, VariableInfo>,
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
            // Logarithmic, but it's fine.
            let start = finalizers.partition_point(|finalizer| finalizer.try_id < exits_group_id);

            // Try to match finalizers. If an expected finalizer could not be matched, it's not
            // a big deal: we can use what Vineflower calls a "predicated finally block", i.e. wrap
            // the `finally` contents in an `if` whose condition is set on "good" exits and unset on
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
                // This comparison iterates over each node in the subtree, but as far as I can tell,
                // the total runtime is still linear thanks to the check for `measure`.
                //
                // The proof sketch goes something like this. Suppose there is a nested sequence of
                // finalizers of lengths a_1, a_2, ..., a_k. If a_1...a_{k-1} match and a_k fails to
                // match, we'll recurse into what we thought was a copy of the k'th finalizer.
                // A term of size a_k can only contain subterms of strictly smaller sizes, so in the
                // worst-case scenario, `a_k > a_1 + ... + a_{k-1}` so that as many nodes are
                // recompared as possible. This implies that `a_k` grows exponentially, and so for
                // the total time we have:
                //     a_1 + (a_1 + a_2) + ... + (a_1 + ... + a_k) = O(a_1 + ... + a_k) = O(n)
                if finalizer.compare(
                    self.arena,
                    &self.var_info,
                    &group.children[i.saturating_sub(finalizer.body.len())..i],
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
                    }
                }

                // Catch bodies typically begin by moving the exception value to stack, but we don't
                // want to fixup `value_var` to `slotN` right now because `slotN` might be used
                // outside `catch` and this would lead to shadowing. We play safe and delay this
                // until a later pass.

                // `finally` blocks typically translate to `catch` bodies as:
                //     slotN = valueM
                //     <body>
                //     valueK = slotN
                //     throw valueK
                // Match this pattern exactly.
                if catch.class.is_none()
                    && catch.body.children.len() >= 3
                    // `slotN = valueM`
                    && let Statement::Basic {
                        stmt:
                            BasicStatement::Assign {
                                target: store_target,
                                value: store_source,
                            },
                        ..
                    } = catch.body.children[0].stmt
                    && let Expression::Variable(store_target) = self.arena[store_target]
                    && store_target.name.namespace == VariableNamespace::Slot
                    && let Expression::Variable(store_source) = self.arena[store_source]
                    && store_source == catch.value_var
                    // `valueK = slotN`
                    && let Statement::Basic {
                        stmt:
                            BasicStatement::Assign {
                                target: load_target,
                                value: load_source,
                            },
                        ..
                    } = catch.body.children[catch.body.children.len() - 2].stmt
                    && let Expression::Variable(load_target) = self.arena[load_target]
                    && load_target.name.namespace == VariableNamespace::Value
                    && let Expression::Variable(load_source) = self.arena[load_source]
                    && load_source == store_target
                    // `throw valueK`
                    && let Statement::Basic {
                        stmt:
                            BasicStatement::Throw { exception },
                        ..
                    } = catch.body.children.last().unwrap().stmt
                    && let Expression::Variable(exception) = self.arena[exception]
                    && exception == load_target
                    // Ensure the variables are not used anywhere else.
                    && [store_target, catch.value_var, exception].iter().all(|var| {
                        self.var_info.get(&var.version).expect("missing var").use_count == 2
                    })
                {
                    let mut finally_children = catch.body.children;
                    // `access_range` is computed before poping elements so that we don't have to
                    // handle the empty `finally` case in a special way. It doesn't affect anyhing
                    // else.
                    let finally_access_range = finally_children[0].meta.access_range.start
                        ..finally_children.last().unwrap().meta.access_range.end;
                    finally_children.pop();
                    finally_children.pop();
                    finally_children.remove(0);
                    let finally_measure = finally_children
                        .iter()
                        .map(|stmt_meta| stmt_meta.meta.measure)
                        .sum();

                    catch.meta.active_index_ranges; // TODO

                    finalizers.push(Finalizer {
                        try_id: try_.id,
                        body: finally_children,
                        measure: finally_measure,
                        access_range: finally_access_range,
                    });
                    let try_ = self.handle_group(try_, &mut Vec::new(), finalizers);
                    let finally = self.handle_group(
                        StmtGroup {
                            id: finally.id,
                            children: finalizers.pop().unwrap().body,
                        },
                        &mut Vec::new(),
                        finalizers,
                    );
                    Statement::try_(try_, Vec::new(), finally)
                } else {
                    let try_ = self.handle_group(try_, &mut Vec::new(), finalizers);
                    let catch_body = self.handle_group(catch.body, &mut Vec::new(), finalizers);
                    Statement::try_(
                        try_,
                        vec![Catch {
                            class: catch.class,
                            value_var: catch.value_var,
                            body: catch_body,
                            meta: catch.meta,
                        }],
                        StmtGroup {
                            id: finally.id,
                            children: Vec::new(),
                        },
                    )
                }
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
