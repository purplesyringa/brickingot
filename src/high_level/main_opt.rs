use super::inlining::Inliner;
use super::{Catch, Meta, Program, Statement, StmtList, StmtMeta};
use crate::ast::{
    Arena, BasicStatement, BinOp, ExprId, Expression, UnaryOp, Variable, VariableNamespace,
};
use crate::exceptions;
use rustc_hash::FxHashMap;

pub fn optimize<'code>(
    arena: &mut Arena<'code>,
    eh_ir: exceptions::Program<'code>,
) -> Program<'code> {
    // This is a bit sketchy, but there shouldn't be any dead variable uses in the arena at this
    // point, and a single linear iteration is better than yet another tree walk. This assumption is
    // a little tricky to support, e.g. `stackless::splitting` has some special handling for this.
    // If this ever becomes too difficult to implement without bugs, we'll have to implement this
    // recursively instead.
    let mut n_var_mentions = FxHashMap::default();
    for expr in arena.iter_mut() {
        if let Expression::Variable(var) = expr {
            *n_var_mentions.entry(*var).or_default() += 1;
        }
    }

    let statements = Optimizer {
        arena,
        n_var_mentions,
        block_info: FxHashMap::default(),
    }
    .handle_stmt_list(eh_ir.statements, None)
    .0;
    Program { statements }
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
        stmt: exceptions::Statement<'code>,
        fallthrough_breaks_from: Option<usize>,
        out: &mut StmtList<'code>,
    ) {
        match stmt {
            exceptions::Statement::Basic(stmt) => self.handle_basic_stmt(stmt, out),

            exceptions::Statement::Block { id, children } => {
                self.handle_block(id, children, fallthrough_breaks_from, out);
            }

            exceptions::Statement::Continue { block_id } => self.handle_continue(block_id, out),

            exceptions::Statement::Break { block_id } => self.handle_break(block_id, out),

            exceptions::Statement::If {
                condition,
                then_children,
            } => {
                self.handle_if(condition, then_children, fallthrough_breaks_from, out);
            }

            exceptions::Statement::Switch { id, key, arms } => {
                self.handle_switch(id, key, arms, fallthrough_breaks_from, out);
            }

            exceptions::Statement::Try {
                try_children,
                catches,
                finally_children,
            } => {
                self.handle_try(
                    try_children,
                    catches,
                    finally_children,
                    fallthrough_breaks_from,
                    out,
                );
            }
        }
    }

    fn handle_basic_stmt(&mut self, mut stmt: BasicStatement, out: &mut StmtList<'code>) {
        // Replace dead `valueN` assignments with computations and drop no-op computations. Dead
        // stack assignments have already been removed in `splitting`, which means that dead
        // `valueN`s have no uses whatsoever (except for the definition itself), so we don't have to
        // focus on that.
        //
        // This step has to run prior to inlining because such no-ops can break the assumption that
        // definitions and uses are consecutive statements (the reason for this assumption is
        // described in more detail in `inlining`).

        // Since versions of unused variables are never merged, all unused variables are guaranteed
        // to have a single mention (the definition itself).
        if let BasicStatement::Assign { target, value } = stmt
            && let Expression::Variable(var) = self.arena[target]
            && var.name.namespace == VariableNamespace::Value
            && *self
                .n_var_mentions
                .get(&var)
                .expect("used variable not mentioned")
                == 1
        {
            // This can turn the assignment into a no-op if the value has no side effects. We
            // consider arithmetic to be a side effect since we want to retain logic present in
            // bytecode, so this can only really happen under the following circumstances:
            // - While initializing method arguments (hence `this` and arguments).
            //   FIXME: we don't currently handle this for multiple reasons, e.g. that those are
            //   assignments to slots, not values; it's not quite clear how to best support this,
            //   since those assignments are closer to forced variable naming than actual
            //   assignments, and we might want to use a different method to represent that.
            // - While saving a double-width value to stack (hence `null`).
            // - When a stack store can be optimized out due to value linking.
            if let/* Expression::This
            | Expression::Argument { .. }
            |*/ Expression::Null
            | Expression::Variable(_) = self.arena[value]
            {
                // It's not really useful to decrease refcount for the defined variable, since it
                // won't ever be mentioned anyway, but it's still useful for the used variable,
                // since it can allow it to become a single-use and thus inlineable. The specific
                // problem we're trying to solve is
                //     stack0 = cond ? if_true : if_false;
                //     value0 = stack0; // unused
                //     // stack1 = value0; <- was used by this dead store, but it was optimized out
                //     use stack0;
                // ...not inlining `stack0` into the use.
                if let Expression::Variable(var) = self.arena[value] {
                    self.arena[value] = Expression::Null;
                    *self.n_var_mentions.get_mut(&var).expect("used variable not mentioned") -= 1;
                }
                return;
            }

            stmt = BasicStatement::Calculate(value);
        }

        let meta = Meta {
            is_divergent: stmt.is_divergent(),
            ..Meta::default()
        };
        out.push(StmtMeta {
            stmt: Statement::Basic(stmt),
            meta,
        });
    }

    fn handle_block(
        &mut self,
        id: usize,
        children: Vec<exceptions::Statement<'code>>,
        fallthrough_breaks_from: Option<usize>,
        out: &mut StmtList<'code>,
    ) {
        self.block_info.insert(
            id,
            BlockInfo {
                n_break_uses: 0,
                n_continue_uses: 0,
            },
        );

        let fallthrough_breaks_from = Some(fallthrough_breaks_from.unwrap_or(id));
        let (mut children, meta) = self.handle_stmt_list(children, fallthrough_breaks_from);

        let block_info = self.block_info.remove(&id).expect("missing block");

        // Since this block stands between an `if`/`switch`/etc. nested inside it and the statements
        // after it, it can prevent inlining `else` branches, `case`s, etc. Therefore, we want to
        // optimize out blocks by removing the block and directly emitting its children under
        // certain conditions.
        //
        // Consider N nested unused blocks with N statements inside the most nested block. If we
        // optimize out every unused block, we'll force time complexity to O(N^2). We *could* do
        // that and generate the input IR in a way that this is not reached, but it'd probably be
        // less hacky to limit the conditions under which such inlining is performed to something
        // like `children.len() == 1`, which guarantees linear time overall.
        //
        // This is less restrictive than it seems.
        //
        // If the block was used by a `continue` prior to any optimizations, the `continue` will
        // stay, since we only touch `break`s during this stage. We can't optimize out such blocks
        // by removal, and it doesn't make sense to move code after the block *into* the block: even
        // if possible, that would just inline everything after a loop into the loop's only exit,
        // which is unnecessary and doesn't improve anything; no inlineable patterns we're trying to
        // match rely on this.
        //
        // Blocks without `continue`s, on the other hand, are guaranteed to be used by a `break`
        // somewhere in the first statement initially. A `break` can only disappear if it was due to
        // an `if`/`switch`/etc., the current block's tail was inlined into that statement, and the
        // `break` was replaced with a fallthrough. Thus the `if`/`switch`/etc. must be the only
        // current child.
        //
        // One problem still exists, though. Normally, each statement is handled by the routines
        // invoked within `handle_stmt_lists` exactly once, but this process causes a single
        // statement to be handled multiple times. That's by design, since we do want to inline
        // multiple tails into a single statement. This forces routines like `inline_switch` to take
        // precautions to work in linear time overall, e.g. by not recursing into all child nodes
        // every time.
        //
        // `inline_expressions` is in a particularly interesting situation, since it recurses not
        // into statements, but into *expressions*; and so invoking `inline_expressions` on
        // a statement multiple times may be catastrophic. But it turns out that we're in luck, if
        // only narrowly.
        //
        // A statement that can be inlined to, like `if`, can only be handled for the second time if
        // it becomes the sole statement in the block; this means that it must be the first
        // statement in `out`. But `inline_expressions` doesn't need to recurse into the first
        // statement, since no definitions can be inlined into uses within that statement. This
        // means that `inline_expressions` will actually touch the `if` for the first time when it
        // stops being the first statement. But that implies that there is either a `continue` to
        // the block or the first statement contains a `break` and thus isn't an assignment that
        // `inline_expressions` can remove; in either case, this block won't be optimized out.

        if block_info.n_continue_uses == 0 && children.len() == 1 {
            // `if`s are guaranteed not to refer to this block at all. Consider:
            //     block #n {
            //         if (!cond) {
            //             break #n;
            //         }
            //         then; // divergent
            //     }
            //     else;
            // ...which we rewrite to:
            //     block #n {
            //         if (!cond) {
            //             // fallthrough
            //         } else {
            //             then; // divergent
            //         }
            //     }
            //     else;
            // If `break #n` is present after the rewrite, we can neither inline `else` into the
            // block, nor move `if` outside the block. So that case is sealed.
            if block_info.n_break_uses == 0 {
                out.extend(children);
                return;
            }

            // `switch`es are nastier. We couldn't remove `break`s equivalent to fallthrough from
            // the `switch` arms, as that would only fallthrough to the next arm; but there is
            // nothing in principle forbidding us from replacing `break`s to this block with
            // `break`s to the switch itself after inlining the tail. This could make this block
            // unnecessary and allow us to optimize it out.
            //
            // We couldn't perform that rewrite immediately, since looking for such `break`s on each
            // iteration would be quadratic, but that doesn't mean we don't want to achieve the goal
            // in a different manner. Instead of replacing block IDs with switch IDs in each
            // `break`, we can replace the switch ID *itself* with the block ID.
            //
            // We can only do this if there are no `break`s from the `switch` itself, since we can't
            // merge two IDs into one, but such `break`s should normally all be gone after inlining.
            if block_info.n_continue_uses == 0
                && let [
                    StmtMeta {
                        stmt:
                            Statement::Switch {
                                id: ref mut switch_id,
                                ..
                            },
                        meta:
                            Meta {
                                n_breaks_from_switch: ref mut n_breaks_from_switch @ 0,
                                ..
                            },
                    },
                ] = children[..]
            {
                *switch_id = id;
                *n_breaks_from_switch = block_info.n_break_uses;
                out.extend(children);
                return;
            }
        }

        out.push(StmtMeta {
            stmt: Statement::Block { id, children },
            meta: Meta {
                is_divergent: meta.is_divergent && block_info.n_break_uses == 0,
                ..Meta::default()
            },
        });
    }

    fn handle_continue(&mut self, block_id: usize, out: &mut StmtList<'code>) {
        self.block_info
            .get_mut(&block_id)
            .expect("missing block")
            .n_continue_uses += 1;
        out.push(StmtMeta {
            stmt: Statement::Continue { block_id },
            meta: Meta {
                is_divergent: true,
                ..Meta::default()
            },
        });
    }

    fn handle_break(&mut self, block_id: usize, out: &mut StmtList<'code>) {
        self.block_info
            .get_mut(&block_id)
            .expect("missing block")
            .n_break_uses += 1;
        out.push(StmtMeta {
            stmt: Statement::Break { block_id },
            meta: Meta {
                is_divergent: true,
                ..Meta::default()
            },
        });
    }

    fn handle_if(
        &mut self,
        condition: ExprId,
        then_children: Vec<exceptions::Statement<'code>>,
        fallthrough_breaks_from: Option<usize>,
        out: &mut StmtList<'code>,
    ) {
        let (then_children, _) = self.handle_stmt_list(then_children, fallthrough_breaks_from);
        out.push(StmtMeta {
            stmt: Statement::If {
                condition,
                condition_inverted: false,
                then_children,
                else_children: Vec::new(),
            },
            meta: Meta {
                is_divergent: false, // since `else` is empty
                ..Meta::default()
            },
        });
    }

    fn handle_switch(
        &mut self,
        id: usize,
        key: ExprId,
        arms: Vec<(Option<i32>, Vec<exceptions::Statement<'code>>)>,
        fallthrough_breaks_from: Option<usize>,
        out: &mut StmtList<'code>,
    ) {
        if arms.is_empty() {
            // Not sure how this can possibly happen, but I'm not certain the bytecode forbids it,
            // so might as well handle this, since `inline_switch` assumes non-empty `switch`.
            return;
        }

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
                // Non-divergent `switch` arms fall through to the next arm, so only the divergence
                // of the last arm matters.
                last_arm_is_divergent = arm_meta.is_divergent;
                (value, children)
            })
            .collect();

        let block_info = self
            .block_info
            .remove(&id)
            .expect("missing block for switch");

        out.push(StmtMeta {
            stmt: Statement::Switch { id, key, arms },
            meta: Meta {
                is_divergent: last_arm_is_divergent && block_info.n_break_uses == 0,
                first_uninlined_switch_arm: 0,
                n_breaks_from_switch: block_info.n_break_uses,
            },
        });
    }

    fn handle_try(
        &mut self,
        try_children: Vec<exceptions::Statement<'code>>,
        catches: Vec<exceptions::Catch<'code>>,
        finally_children: Vec<exceptions::Statement<'code>>,
        fallthrough_breaks_from: Option<usize>,
        out: &mut StmtList<'code>,
    ) {
        let (try_children, try_meta) = self.handle_stmt_list(try_children, fallthrough_breaks_from);
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
                }
            })
            .collect();
        // `finally` is not really part of control flow: it can be entered from any point and it
        // transfers control to an arbitrary point after finishing. For example, it can rethrow
        // an ongoing exception, `break` or `continue` a loop, or `return`; meaning that its
        // fallthrough target is undefined.
        let (finally_children, finally_meta) = self.handle_stmt_list(finally_children, None);
        // `finally` is executed on every exit path in sequence after the previous code.
        is_divergent |= finally_meta.is_divergent;
        out.push(StmtMeta {
            stmt: Statement::Try {
                try_children,
                catches,
                finally_children,
            },
            meta: Meta {
                is_divergent,
                ..Meta::default()
            },
        });
    }

    fn handle_stmt_list(
        &mut self,
        stmts: Vec<exceptions::Statement<'code>>,
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
                    if let exceptions::Statement::Break { block_id } = next_stmt {
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

        self.inline_tails(&mut out, fallthrough_breaks_from);

        let last_stmt_is_divergent = out
            .last()
            .is_some_and(|stmt_meta| stmt_meta.meta.is_divergent);
        let meta = Meta {
            is_divergent: last_stmt_is_divergent,
            ..Meta::default()
        };
        (out, meta)
    }

    fn inline_tails(
        &mut self,
        stmts: &mut StmtList<'code>,
        fallthrough_breaks_from: Option<usize>,
    ) {
        // If a statement with multiple children has a single non-divergent arm, it might make sense
        // to inline every statement after it into the arm. This is useful for decoding `if`,
        // `switch`, and `try`, which start with (almost) empty arms that are slowly populated by
        // inlining.
        //
        // This is easier to understand on an example `if` lowering:
        //         if (!cond) goto after_then;
        //         then;
        //         goto end;
        //     after_then:
        //         else;
        //     end:
        // If `then` diverges, `goto end` will be absent, so we can't rely on `goto end` to
        // determine where `else` starts and ends. Even if it is present, it could point to
        // something other than the first instruction after `else` due to jump threading.
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
        //
        // Specifically due to the goal of this pass -- inlining everything that can possibly be
        // inlined --  we strive to make everything as nested and compact as possible, e.g. prefer
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
        // the decompiled code ugly, we can always adjust it at a later pass after inlining is
        // complete.
        //
        // We don't *always* force the inlining, though, since we only need to force nesting to
        // detect things like ternaries, and otherwise it's better to retain the structure of the
        // source.

        for i in (0..stmts.len()).rev() {
            // This could be nicer :/ We want to pass both the statement and the tail of the vector
            // to the individual inliners, but we only want to move out the tail conditionally.
            // There is no `split_at_mut`-like helper for `split_off`, so we have to do this mess.
            let mut stmt_meta = core::mem::replace(
                &mut stmts[i],
                StmtMeta {
                    meta: Meta::default(),
                    stmt: Statement::Basic(BasicStatement::ReturnVoid),
                },
            );

            let tail_is_empty = i == stmts.len() - 1;
            let take_tail = || stmts.split_off(i + 1);

            match stmt_meta.stmt {
                Statement::If { .. } => {
                    self.inline_if(&mut stmt_meta, take_tail, fallthrough_breaks_from);
                }
                // switches don't like inlining empty tails, see `inline_switch` for more.
                Statement::Switch { .. } if !tail_is_empty => {
                    self.inline_switch(&mut stmt_meta, take_tail, fallthrough_breaks_from);
                }
                _ => {}
            }

            stmts[i] = stmt_meta;
        }
    }

    fn inline_if(
        &mut self,
        stmt_meta: &mut StmtMeta<'code>,
        take_tail: impl FnOnce() -> StmtList<'code>,
        tail_fallthrough_breaks_from: Option<usize>,
    ) {
        let Statement::If {
            condition,
            condition_inverted,
            then_children,
            else_children,
        } = &mut stmt_meta.stmt
        else {
            panic!("inline_if invoked on something other than if");
        };

        if !list_is_divergent(then_children) {
            return;
        }

        // Not strictly necessary, but it's easier this way. Saves us the worry about "what if
        // `else_children` is not a single expression and `stmts[i + 1..]` is not a single
        // expression, but their concatenation is" that we can't resolve efficiently. Overall,
        // handling this case is just unnecessary in practice.
        if !else_children.is_empty() {
            return;
        }

        *else_children = take_tail();

        // This movement may cause some `break`s/`continue`s within `then` that previously jumped
        // over `else` to become equivalent to fallthrough. We cannot fix that now without making
        // the code quadratic, but we don't need to do that in the general case: it will only affect
        // the quality of this pass if `then` would otherwise become a single `Assign`, so we only
        // need to consider the last statement in `then`.
        //
        // We don't have to optimize out `continue`s here because ternary branches never jump
        // upward, and it'd be tricky to attempt it anyway because the meaning of `continue` is
        // different between blocks and loops, and we'd rather not think about that right now.
        if let Some(tail_fallthrough_breaks_from) = tail_fallthrough_breaks_from
            && then_children
                .pop_if(|stmt| {
                    matches!(
                        stmt.stmt,
                        Statement::Break { block_id }
                            if block_id == tail_fallthrough_breaks_from,
                    )
                })
                .is_some()
        {
            self.block_info
                .get_mut(&tail_fallthrough_breaks_from)
                .expect("missing block")
                .n_break_uses -= 1;
        }

        stmt_meta.meta = Meta {
            is_divergent: list_is_divergent(then_children) && list_is_divergent(else_children),
            ..Meta::default()
        };

        if !*condition_inverted {
            // javac usually compiles `if`s with `if (!cond)`, so we swap `then` and `else` branches
            // and invert the condition to get closer to source. This is only performed the first
            // time `if` is considered. This also allows the same `if` to be recognized the second
            // time to parse `then` and `else` branches.
            //
            // The exception to "usually" here is exit/continue conditions in loops and
            // `||`/`&&`/`?:` lowering, which we'll handle later.
            core::mem::swap(then_children, else_children);
            *condition_inverted = true;
            return;
        }

        // We've just populated both branches.

        // See if this looks like a ternary. We don't have to worry about inlining it into anything
        // because it's the last statement (and thus it'll be inlined as part of the outer block);
        // and we don't have to worry about inlining expressions *into* the ternary branches because
        // that'd be unsound due to side effects anyway, and javac always generates such expressions
        // inside `if` branches.
        if let [
            StmtMeta {
                stmt:
                    Statement::Basic(BasicStatement::Assign {
                        target: then_target,
                        value: then_value,
                    }),
                ..
            },
        ] = then_children[..]
            && let Expression::Variable(then_var) = self.arena[then_target]
            // `slotN` targets are normal `if`s, not ternaries; it'd be *sound* to rewrite, but
            // farther from source.
            && then_var.name.namespace == VariableNamespace::Stack
            && let [
                StmtMeta {
                    stmt:
                        Statement::Basic(
                                BasicStatement::Assign {
                                    target: else_target,
                                    value: else_value,
                                },
                        ),
                    ..
                },
            ] = else_children[..]
            && let Expression::Variable(else_var) = self.arena[else_target]
            && then_var == else_var
        {
            let condition = self.invert_condition(*condition);

            stmt_meta.stmt = Statement::Basic(BasicStatement::Assign {
                target: then_target,
                value: self.arena.alloc(Expression::Ternary {
                    condition,
                    branches: [then_value, else_value],
                }),
            });
            // Decrement refcount for the variable so that it can be inlined.
            self.arena[else_target] = Expression::Null;
            *self
                .n_var_mentions
                .get_mut(&else_var)
                .expect("used variable not mentioned") -= 1;
        }
    }

    // This consumes the `condition` (i.e. assumes it isn't used anywhere else and can be inlined
    // directly into the output).
    fn invert_condition(&mut self, condition: ExprId) -> ExprId {
        match self.arena[condition] {
            // Occasionally used as `true`/`false`.
            Expression::ConstInt(int) => self.arena.int(if int == 0 { 1 } else { 0 }),

            Expression::BinOp { ref mut op, .. } => {
                *op = match op {
                    BinOp::Eq => BinOp::Ne,
                    BinOp::Ne => BinOp::Eq,
                    BinOp::Lt => BinOp::Ge,
                    BinOp::Le => BinOp::Gt,
                    BinOp::Gt => BinOp::Le,
                    BinOp::Ge => BinOp::Lt,
                    _ => {
                        return self.arena.alloc(Expression::UnaryOp {
                            op: UnaryOp::Not,
                            argument: condition,
                        });
                    }
                };
                condition
            }

            Expression::UnaryOp {
                op: UnaryOp::Not,
                argument,
            } => argument,

            _ => self.arena.alloc(Expression::UnaryOp {
                op: UnaryOp::Not,
                argument: condition,
            }),
        }
    }

    fn inline_switch(
        &mut self,
        stmt_meta: &mut StmtMeta<'code>,
        take_tail: impl FnOnce() -> StmtList<'code>,
        tail_fallthrough_breaks_from: Option<usize>,
    ) {
        let Some(arm_id) = self.find_switch_inline_target(stmt_meta) else {
            return;
        };
        let Statement::Switch { id, arms, .. } = &mut stmt_meta.stmt else {
            panic!("inline_switch invoked on something other than switch");
        };
        let is_last_arm = arm_id == arms.len() - 1;
        let arm = &mut arms[arm_id].1;

        // Inline into this arm.
        *arm = take_tail();

        // If the tail is not divergent and this is not the last arm, execution will continue to the
        // next arm instead of breaking from the switch, so we have to add a `break` in this case.
        if is_last_arm || list_is_divergent(arm) {
            return;
        }

        let break_id = tail_fallthrough_breaks_from.unwrap_or(*id);

        // The obvious exception is if we *want* execution to continue to the next arm. If the tail
        // and the next arm would reach the same target, i.e.: if the next non-empty arm contains
        // the same `break` that we want to insert, we shouldn't do that, since it'd make the
        // `break` non-unique and prevent further inlining.
        //
        // This check is a little ugly, but still linear, since for each inlined arm, we only scan
        // the statements corresponding to the next inlineable arm once.
        let fallthrough_to_next_arm = arms[arm_id + 1..]
            .iter()
            .find(|next_arm| !next_arm.1.is_empty())
            .is_some_and(|next_arm| {
                matches!(
                    next_arm.1[..],
                    [StmtMeta {
                        stmt: Statement::Break { block_id },
                        ..
                    }] if block_id == break_id,
                )
            });
        if fallthrough_to_next_arm {
            return;
        }

        // `arm.push` would be nicer, but we've just invalidated the borrow.
        arms[arm_id].1.push(StmtMeta {
            stmt: Statement::Break { block_id: break_id },
            meta: Meta {
                is_divergent: true,
                ..Meta::default()
            },
        });
        if break_id == *id {
            // The `switch` has already been popped from `block_info`, so we have to patch this
            // variable instead. A bit ugly.
            stmt_meta.meta.n_breaks_from_switch += 1;
        } else {
            self.block_info
                .get_mut(&break_id)
                .expect("missing block")
                .n_break_uses += 1;
        }
    }

    fn find_switch_inline_target(&mut self, stmt_meta: &mut StmtMeta<'code>) -> Option<usize> {
        let Statement::Switch { id, arms, .. } = &mut stmt_meta.stmt else {
            panic!("find_switch_inline_target invoked on something other than switch");
        };

        // Used a bit later, calculated here due to borrowck.
        let last_arm_is_divergent = list_is_divergent(&arms.last().expect("switch with no arms").1);

        // A switch with `N` arms can be inlined to `N` times, so we don't want to iterate over
        // `arms` here, lest we get quadratic complexity. Since switch arms are ordered by
        // increasing target, we can expect to inline arms in the same order they are listed in, so
        // this can be turned into a linear scan by passing a bit of metadata between iterations.
        let i = &mut stmt_meta.meta.first_uninlined_switch_arm;
        let arms_len = arms.len();
        while *i < arms.len() {
            let arm = &mut arms[*i].1;
            *i += 1;
            let is_last_arm = *i == arms_len;

            // A lot of complexity here stems from the fact that fallthrough from an arm continues
            // to the next arm instead of breaking out of the `switch`.
            //
            // For one thing, it's harder to find which arms are ready to accept the tail than with
            // `if`, where we could just use an empty arm. Instead, we want to find either an arm
            // containing a single `break` equivalent to a fallthrough *from the switch* (which, for
            // non-empty tails, can only be a break from the switch specifically), or an empty last
            // arm.
            //
            // This also means that, when we do inline an arm, we cannot replace *any* breaks with
            // fallthroughs, except for breaks in the last arm.
            //
            // Finally, inlining into an arm is only allowed if no other arm can enter the tail,
            // i.e. if the `switch` would be divergent without this arm.
            let n_breaks = &mut stmt_meta.meta.n_breaks_from_switch;

            // Theoretically, multiple arms can match, but that only happens if multiple arms have
            // the same target in bytecode, and we have already optimized such arms to
            // `case 1: ... case n: break #m;` during IR construction in `Structurizer::emit_stmt`.
            // Thus there will be at most one matching arm that we need to inline to.
            //
            // On the flip side, this means that if there are ways to escape the `switch` without
            // going through the matched arm (i.e. with `break`s or fallthrough from the last arm),
            // we can't really do much and have to abort inlining.

            if arm.is_empty() {
                if !is_last_arm {
                    // Can't inline into this arm right now. This implies that this arm will never
                    // be inlined to, since the tail will either be inlined into another, later arm,
                    // or be left as-is after the switch, preventing any other inlines. The only
                    // exception is an empty tail, which we've prefiltered. Thus we can advance to
                    // the next arm safely.
                    continue;
                }
                // Other arms can only be non-divergent (excluding fallthrough into this arm) if
                // they have `break`s.
                if *n_breaks > 0 {
                    return None;
                }
            } else {
                // We don't need to care about equivalent `break`s since a non-empty tail implies
                // there is no other way to jump to after the switch.
                let is_break = matches!(
                    arm[..],
                    [StmtMeta {
                        stmt: Statement::Break { block_id },
                        ..
                    }] if block_id == *id,
                );
                if !is_break {
                    continue;
                }
                // Other arms can only be non-divergent (excluding fallthrough into this arm) if
                // they have `break`s or if the last arm is non-divergent. There is a special case
                // if *this* is the last arm; but since it contains `break`, it's automatically
                // considered divergent, so this test will work just fine.
                if *n_breaks > 1 || !last_arm_is_divergent {
                    return None;
                }
                // Inlining overwrites this `break`.
                *n_breaks -= 1;
            }

            return Some(*i - 1);
        }

        None
    }
}

fn list_is_divergent<'code>(stmts: &StmtList<'code>) -> bool {
    stmts.last().is_some_and(|stmt| stmt.meta.is_divergent)
}
