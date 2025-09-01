use super::inlining::Inliner;
use super::{Catch, Meta, Statement, StmtList, StmtMeta};
use crate::arena::Arena;
use crate::ast::{Expression, Variable};
use crate::structured;
use rustc_hash::FxHashMap;

pub fn optimize<'code>(
    arena: &mut Arena<'code>,
    structured_ir: Vec<structured::Statement<'code>>,
) -> Vec<StmtMeta<'code>> {
    // This is a bit scetchy, but there shouldn't be any dead variable uses in the arena at this
    // point, and a single linear iteration is better than yet another tree walk. This assumption is
    // a little tricky to support, e.g. `stackless::splitting` has some special handling for this.
    let mut n_var_mentions = FxHashMap::default();
    for expr in arena.iter_mut() {
        if let Expression::Variable(var) = expr {
            *n_var_mentions.entry(*var).or_default() += 1;
        }
    }

    Optimizer {
        arena,
        n_var_mentions,
        block_info: FxHashMap::default(),
    }
    .handle_stmt_list(structured_ir, None)
    .0
}

struct Optimizer<'arena, 'code> {
    arena: &'arena mut Arena<'code>,
    n_var_mentions: FxHashMap<Variable, usize>,
    block_info: FxHashMap<usize, BlockInfo>,
}

struct BlockInfo {
    n_break_uses: usize,
    n_continue_uses: usize,
}

impl<'code> Optimizer<'_, 'code> {
    fn handle_stmt(
        &mut self,
        stmt: structured::Statement<'code>,
        fallthrough_breaks_from: Option<usize>,
        out: &mut StmtList<'code>,
    ) {
        out.push(match stmt {
            structured::Statement::Basic { index, stmt } => {
                let meta = Meta {
                    is_divergent: stmt.is_divergent(),
                };
                StmtMeta {
                    stmt: Statement::Basic { index, stmt },
                    meta,
                }
            }

            structured::Statement::Block { id, children } => {
                self.block_info.insert(
                    id,
                    BlockInfo {
                        n_break_uses: 0,
                        n_continue_uses: 0,
                    },
                );

                let fallthrough_breaks_from = Some(fallthrough_breaks_from.unwrap_or(id));
                let (children, meta) = self.handle_stmt_list(children, fallthrough_breaks_from);

                let block_info = self.block_info.remove(&id).expect("missing block");

                // If there's an `if` inside this block, this block might stop the `else` branch
                // from being inlined into the `if`
                //
                // This is, however, trickier than it seems, since blocks may be used by `break`s
                // and `continue`s, and whether to inline or not inline the `then` or `else`
                // branches in this case is less clear.
                //
                // Consider
                //     block #n {
                //         ...
                //         if (!cond) {
                //             break #n;
                //         }
                //         then; // divergent
                //     }
                //     else;
                // ...which we rewrite to:
                //     block #n {
                //         ...
                //         if (!cond) {
                //             // fallthrough
                //         } else {
                //             then; // divergent
                //         }
                //     }
                //     else;
                //
                // If `break #n` is present after the rewrite, we cannot inline `else` into the
                // block and we cannot move `if` outside the block.
                //
                // If `#n` is now unused, we can remove the block altogether; in fact, in this case,
                // `...` is guaranteed to be empty.
                //
                // But what if there is no (other) `break #n`, but plenty of `continue #n`? In this
                // case, `#n` is a loop. We know that `then;` must contain `continue #n`, or the
                // block would be split into two. Thus `if (!cond)` is the only exit from this loop;
                // it's likely similar to `do { ... } while (cond);`. Inlining `else;` into
                // `break #n` would mean inlining the code after the loop into its only exit. This
                // would complicate code without allowing any useful constructs to match, like
                // ternaries, since the stack variable written by the ternary branches cannot be
                // read across loop iterations, and that's what would happen here. So while we
                // *could* inline `else;` in principle, it would not be useful in any way that
                // matters.
                //
                // The solution is thus as simple as only removing unused blocks.
                if block_info.n_break_uses == 0 && block_info.n_continue_uses == 0 {
                    out.extend(children);
                    return;
                }

                StmtMeta {
                    stmt: Statement::Block { id, children },
                    meta: Meta {
                        is_divergent: meta.is_divergent && block_info.n_break_uses == 0,
                    },
                }
            }

            structured::Statement::Continue { block_id } => {
                self.block_info
                    .get_mut(&block_id)
                    .expect("missing block")
                    .n_continue_uses += 1;
                StmtMeta {
                    stmt: Statement::Continue { block_id },
                    meta: Meta { is_divergent: true },
                }
            }

            structured::Statement::Break { block_id } => {
                self.block_info
                    .get_mut(&block_id)
                    .expect("missing block")
                    .n_break_uses += 1;
                StmtMeta {
                    stmt: Statement::Break { block_id },
                    meta: Meta { is_divergent: true },
                }
            }

            structured::Statement::If {
                condition,
                then_children,
            } => {
                let (then_children, _) =
                    self.handle_stmt_list(then_children, fallthrough_breaks_from);
                StmtMeta {
                    stmt: Statement::If {
                        condition,
                        condition_inverted: false,
                        then_children,
                        else_children: Vec::new(),
                    },
                    meta: Meta {
                        is_divergent: false, // since `else` is empty
                    },
                }
            }

            structured::Statement::Switch { id, key, arms } => {
                self.block_info.insert(
                    id,
                    BlockInfo {
                        n_break_uses: 0,
                        n_continue_uses: 0,
                    },
                );

                let n_arms = arms.len();
                let fallthrough_breaks_from = Some(fallthrough_breaks_from.unwrap_or(id));

                let mut last_arm_is_divergent = false;
                let arms = arms
                    .into_iter()
                    .enumerate()
                    .map(|(i, (value, children))| {
                        let (children, arm_meta) = self.handle_stmt_list(
                            children,
                            if i == n_arms - 1 {
                                fallthrough_breaks_from
                            } else {
                                None
                            },
                        );
                        // Non-divergent `switch` arms fall through to the next arm.
                        last_arm_is_divergent = arm_meta.is_divergent;
                        (value, children)
                    })
                    .collect();

                let block_info = self.block_info.remove(&id).expect("missing block");

                StmtMeta {
                    stmt: Statement::Switch { id, key, arms },
                    meta: Meta {
                        is_divergent: last_arm_is_divergent && block_info.n_break_uses == 0,
                    },
                }
            }

            structured::Statement::Try { children, catches } => {
                let (children, try_meta) = self.handle_stmt_list(children, fallthrough_breaks_from);
                let mut is_divergent = try_meta.is_divergent;
                let catches = catches
                    .into_iter()
                    .map(|catch| {
                        let (children, catch_meta) =
                            self.handle_stmt_list(catch.children, fallthrough_breaks_from);
                        is_divergent &= catch_meta.is_divergent;
                        Catch {
                            class: catch.class,
                            children,
                            active_range: catch.active_range,
                        }
                    })
                    .collect();
                StmtMeta {
                    stmt: Statement::Try { children, catches },
                    meta: Meta { is_divergent },
                }
            }
        });
    }

    fn handle_stmt_list(
        &mut self,
        stmts: Vec<structured::Statement<'code>>,
        fallthrough_breaks_from: Option<usize>,
    ) -> (StmtList<'code>, Meta) {
        let mut out = Vec::with_capacity(stmts.len()); // only approximate, but that's fine

        let mut stmts = stmts.into_iter().peekable();
        while let Some(stmt) = stmts.next() {
            self.handle_stmt(
                stmt,
                if let Some(next_stmt) = stmts.peek() {
                    // This can happen in the middle of a `switch` if we `break` from a higher-level
                    // block.
                    if let structured::Statement::Break { block_id } = next_stmt {
                        Some(*block_id)
                    } else {
                        None
                    }
                } else {
                    fallthrough_breaks_from
                },
                &mut out,
            );
        }

        out = Inliner::inline_expressions(
            core::mem::take(&mut out),
            self.arena,
            &self.n_var_mentions,
        );

        self.decompile_ifs(&mut out, fallthrough_breaks_from);

        let last_stmt_is_divergent = out
            .last()
            .is_some_and(|stmt_meta| stmt_meta.meta.is_divergent);
        let meta = Meta {
            is_divergent: last_stmt_is_divergent,
        };
        (out, meta)
    }

    fn decompile_ifs(
        &mut self,
        stmts: &mut StmtList<'code>,
        fallthrough_breaks_from: Option<usize>,
    ) {
        // `if` statements are typically compiled as
        //         if (!cond) goto after_then;
        //         then;
        //         goto end;
        //     after_then:
        //         else;
        //     end:
        // ...but if `then` diverges, `goto end` won't be present. Even if it is present, it could
        // point to something other than the first instruction after `else` due to jump threading.
        // `goto after_then` is also subject to jump threading, so really, the only common pattern
        // is:
        //     if (cond) <divergent>
        //     then; // no entry other than fallthrough
        // ...which we decompile as
        //     block #n {
        //         ...
        //         if (cond) <divergent>;
        //         then;
        //     }
        // This is sufficient to recognize
        //     block #1 {
        //         block #2 {
        //             if (!cond) break #2;
        //             then;
        //             break #1;
        //         }
        //         else;
        //     }
        // ->
        //     block #1 {
        //         if (cond) {
        //             then;
        //             break #1;
        //         }
        //         else;
        //     }
        // ->
        //     if (cond) {
        //         then;
        //     } else {
        //         else;
        //     }
        // ...assuming no-op `break`s and unused blocks are removed.

        // Specifically due to the goal of this pass, we strive to make everything as nested and
        // compact as possible, e.g. prefer
        //     if (cond) {
        //         then;
        //     } else {
        //         else;
        //     }
        // over
        //     if (cond) {
        //         then;
        //         break;
        //     }
        //     else;
        // even if `then` is short and `else` is long, since it's easier to pattern-match and
        // analyze and will not lead to false negatives in ternaries and similar cases. If we find
        // the decompiled code ugly, we can always adjust it at a later pass.

        for i in (0..stmts.len()).rev() {
            if let Statement::If {
                then_children,
                else_children,
                ..
            } = &mut stmts[i].stmt
                && list_is_divergent(then_children)
                // Not strictly necessary, but it's easier this way. Saves us the worry about "what
                // if `else_children` is not a single expression and `stmts[i + 1..]` is not
                // a single expression, but their concatenation is" that we can't resolve
                // efficiently.
                && else_children.is_empty()
            {
                // Inline the rest of `stmts` into `else_children`.
                let local_else_children = stmts.split_off(i + 1);

                let Statement::If {
                    condition_inverted,
                    then_children,
                    else_children,
                    ..
                } = &mut stmts[i].stmt
                else {
                    unreachable!()
                };
                *else_children = local_else_children;

                // This movement may cause some `break`s/`continue`s within `then` that previously
                // jumped over `else` to become equivalent to fallthrough. We cannot fix that now
                // without making the code quadratic, but we don't need to do that in the general
                // case: it will only affect the quality of this pass if `then` would otherwise
                // become a single `Assign`, so we only need to consider the last statement in
                // `then`.
                //
                // We don't have to optimize out `continue`s here because ternary branches never
                // jump upward, and it'd be tricky to attempt it anyway because the meaning of
                // `continue` is different between blocks and loops, and we'd rather not think about
                // that right now.
                if let Some(fallthrough_breaks_from) = fallthrough_breaks_from
                    && then_children
                        .pop_if(|stmt| {
                            matches!(
                                stmt.stmt,
                                Statement::Break { block_id }
                                    if block_id == fallthrough_breaks_from,
                            )
                        })
                        .is_some()
                {
                    self.block_info
                        .get_mut(&fallthrough_breaks_from)
                        .expect("missing block")
                        .n_break_uses -= 1;
                }

                if !*condition_inverted {
                    // javac usually compiles `if`s with `if (!cond)`, so we swap `then` and `else`
                    // branches and invert the condition to get closer to source. This is only
                    // performed the first time `if` is considered. This also allows the same `if`
                    // to be recognized the second time to parse `then` and `else` branches.
                    //
                    // The exception to "usually" here is exit/continue conditions in loops and
                    // `||`/`&&`/`?:` lowering, which we'll handle later.
                    core::mem::swap(then_children, else_children);
                    *condition_inverted = true;
                }

                stmts[i].meta = Meta {
                    is_divergent: list_is_divergent(&then_children)
                        && list_is_divergent(&else_children),
                };
            }
        }
    }
}

fn list_is_divergent<'code>(stmts: &StmtList<'code>) -> bool {
    stmts.last().is_some_and(|stmt| stmt.meta.is_divergent)
}
