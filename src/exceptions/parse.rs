use super::{CatchMeta, Ir, Program};
use crate::ast::{Catch, Statement, StmtList};
use crate::structured;
use core::cell::Cell;
use rustc_hash::FxHashSet;

pub fn parse_try_blocks(ir: structured::Program) -> Program {
    // Our plan:
    // - Inline tails into `catch`.
    // - Recognize every `catch (...)` that looks like `finally`.

    let mut analyzer = Analyzer {
        blocks_with_breaks: FxHashSet::default(),
    };
    analyzer.handle_stmt_list(&ir);

    let catch_inliner = CatchInliner {
        blocks_with_breaks: analyzer.blocks_with_breaks,
    };
    catch_inliner.handle_stmt_list(ir, None).0
}

struct Analyzer {
    blocks_with_breaks: FxHashSet<usize>,
}

impl<'code> Analyzer {
    fn handle_stmt_list(&mut self, stmts: &[Statement<structured::Ir>]) {
        for stmt in stmts {
            self.handle_stmt(stmt);
        }
    }

    fn handle_stmt(&mut self, stmt: &Statement<structured::Ir>) {
        match stmt {
            Statement::Basic { .. } => {}
            Statement::Block { children, .. } => self.handle_stmt_list(children),
            Statement::Continue { .. } => {}
            Statement::Break { block_id, .. } => {
                self.blocks_with_breaks.insert(*block_id);
            }
            Statement::If { then_children, .. } => self.handle_stmt_list(then_children),
            Statement::Switch { arms, .. } => {
                for (_, children) in arms {
                    self.handle_stmt_list(children);
                }
            }
            Statement::Try {
                try_children,
                catches,
                finally_children,
                ..
            } => {
                self.handle_stmt_list(try_children);
                for catch in catches {
                    self.handle_stmt_list(&catch.children);
                }
                self.handle_stmt_list(finally_children);
            }
        }
    }
}

struct CatchInliner {
    blocks_with_breaks: FxHashSet<usize>,
}

/// A linked list of reversed vectors of statements that are known to be executed by fallthrough
/// after the current statement, and *only* by that fallthrough. The statements always directly
/// follow the current statement without skipping any statements.
///
/// This has a weird data structure, but it's forced by lifetimes.
struct TailNode<'a> {
    list: &'a Cell<StmtList<Ir>>,
    is_divergent: bool,
    next: Tail<'a>,
}

type Tail<'a> = Option<&'a TailNode<'a>>;

struct Meta {
    is_divergent: bool,
}

impl<'code> CatchInliner {
    fn handle_stmt_list(
        &self,
        stmts: StmtList<structured::Ir>,
        tail: Tail<'_>,
    ) -> (StmtList<Ir>, Meta) {
        let mut out = Vec::with_capacity(stmts.len());
        let mut is_divergent = false;
        for stmt in stmts.into_iter().rev() {
            let (stmt, stmt_meta) = self.handle_stmt(
                stmt,
                Some(&TailNode {
                    list: Cell::from_mut(&mut out),
                    is_divergent,
                    next: tail,
                }),
            );
            // Adjust `is_divergent` after each iteration, since the recursive call could have
            // consumed `out`.
            if out.is_empty() {
                is_divergent = stmt_meta.is_divergent;
            }
            out.push(stmt);
        }
        if out.is_empty() {
            is_divergent = false;
        }
        out.reverse();
        (out, Meta { is_divergent })
    }

    fn handle_stmt(
        &self,
        stmt: Statement<structured::Ir>,
        tail: Tail<'_>,
    ) -> (Statement<Ir>, Meta) {
        match stmt {
            Statement::Basic { stmt, .. } => {
                let is_divergent = stmt.is_divergent();
                (Statement::basic(stmt), Meta { is_divergent })
            }

            Statement::Block { id, children, .. } => {
                let has_break = self.blocks_with_breaks.contains(&id);
                let (children, meta) =
                    self.handle_stmt_list(children, if has_break { None } else { tail });
                (
                    Statement::block(id, children),
                    Meta {
                        is_divergent: meta.is_divergent && !has_break,
                    },
                )
            }

            Statement::Continue { block_id, .. } => {
                (Statement::continue_(block_id), Meta { is_divergent: true })
            }

            Statement::Break { block_id, .. } => {
                (Statement::break_(block_id), Meta { is_divergent: true })
            }

            Statement::If {
                condition,
                then_children,
                ..
            } => (
                Statement::if_(
                    condition,
                    self.handle_stmt_list(then_children, None).0,
                    Vec::new(),
                ),
                Meta {
                    is_divergent: false, // `else` is convergent
                },
            ),

            Statement::Switch { id, key, arms, .. } => {
                let has_break = self.blocks_with_breaks.contains(&id);
                let mut is_divergent = false;
                let arms = arms
                    .into_iter()
                    // Strictly speaking, it might not be `None` for the last arm, but we never
                    // generate `try` inside `switch` cases on the previous passes so it doesn't
                    // matter.
                    .map(|(value, children)| {
                        let (children, meta) = self.handle_stmt_list(children, None);
                        is_divergent = meta.is_divergent; // normally divergent iff the last case is
                        (value, children)
                    })
                    .collect();
                (
                    Statement::switch(id, key, arms),
                    Meta {
                        is_divergent: is_divergent && !has_break,
                    },
                )
            }

            Statement::Try {
                try_children,
                mut catches,
                ..
            } => {
                let (try_children, try_meta) = self.handle_stmt_list(try_children, None);

                assert_eq!(catches.len(), 1, "must have a single catch");
                let catch = catches.pop().unwrap();

                let (mut catch_children, mut catch_meta) =
                    self.handle_stmt_list(catch.children, None);

                if try_meta.is_divergent {
                    // Inline tail. This can inline more than just the `catch` body: it can also
                    // inline e.g. the iteration statement of a `for` loop.
                    //
                    // This is somewhat confusing, but ultimatley does not break any invariant. We
                    // need to preserve the invariant that every *block* either has a `break` to it
                    // or ends with something containing a `continue` to it, but we're inlining into
                    // `catch`, not into a block.
                    //
                    // The loop decoder is prepared to deal with this mess, since it has to deal
                    // with overinlining into an `if`'s `else` branch anyway.
                    let mut it = tail;
                    while let Some(&TailNode {
                        list,
                        is_divergent,
                        next,
                    }) = it
                    {
                        catch_children.extend(list.take().into_iter().rev());
                        catch_meta.is_divergent = is_divergent;
                        it = next;
                    }
                }

                (
                    Statement::try_(
                        try_children,
                        vec![Catch {
                            class: catch.class,
                            children: catch_children,
                            meta: CatchMeta {
                                active_index_ranges: catch.meta.active_index_ranges,
                            },
                        }],
                        Vec::new(),
                    ),
                    Meta {
                        is_divergent: try_meta.is_divergent && catch_meta.is_divergent,
                    },
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
