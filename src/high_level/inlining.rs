// This module is solely responsible for merging definitions into uses; it does not create any new
// definitions, like `?:`. That's the responsibility of `Optimizer`.

use super::{Statement, StmtList, StmtMeta};
use crate::ast::{Arena, BasicStatement, ExprId, Expression, Variable, VariableNamespace};
use rustc_hash::FxHashMap;

pub struct Inliner<'a, 'code> {
    arena: &'a Arena<'code>,
    n_var_mentions: &'a FxHashMap<Variable, usize>,
    rev_stmts: core::iter::Peekable<core::iter::Rev<alloc::vec::IntoIter<StmtMeta<'code>>>>,
    inlined_exprs: Vec<(ExprId, ExprId)>, // (use, value)
}

impl<'a, 'code> Inliner<'a, 'code> {
    pub fn inline_expressions(
        stmts: StmtList<'code>,
        arena: &mut Arena<'code>,
        n_var_mentions: &FxHashMap<Variable, usize>,
    ) -> StmtList<'code> {
        let mut inliner = Inliner {
            arena,
            n_var_mentions,
            // Since we want to handle cases like
            //     a := expr1
            //     b := expr2
            //     c := a + b
            // ...we need to iterate over statements and subexpressions in reverse order.
            rev_stmts: stmts.into_iter().rev().peekable(),
            inlined_exprs: Vec::new(),
        };
        let out = inliner.handle_stmt_list();
        // All modifications are saved to `inlined_exprs` and then applied at once -- here.
        for (use_expr_id, value_expr_id) in inliner.inlined_exprs {
            // We don't care about the new value of `arena[value_expr_id]`, so might as well just do
            // this; should be somewhat cheaper than alternatives.
            arena.swap(use_expr_id, value_expr_id);
        }
        out
    }

    fn handle_stmt_list(&mut self) -> StmtList<'code> {
        let mut out = Vec::new();

        while let Some(stmt_meta) = self.rev_stmts.next() {
            // No need to recurse into the first statement, since its uses can never be resolved to
            // any assignment. This `if` is not a micro-optimization and is much more important than
            // it seems: recursing unconditionally can cause the overall time complexity of
            // optimization to become quadratic. See the comment in `Optimizer::handle_block` for
            // more information about why this matters.
            if self.rev_stmts.peek().is_some() {
                let subexprs = match &stmt_meta.stmt {
                    Statement::Basic(stmt) => stmt.subexprs(),
                    Statement::If { condition, .. } => {
                        BasicStatement::subexprs_from_single(*condition)
                    }
                    Statement::Switch { key, .. } => BasicStatement::subexprs_from_single(*key),
                    Statement::Block { .. }
                    | Statement::Continue { .. }
                    | Statement::Break { .. }
                    | Statement::Try { .. } => BasicStatement::subexprs_empty(),
                };

                for expr_id in subexprs.rev() {
                    self.handle_expr(expr_id);
                }
            }

            out.push(stmt_meta);
        }

        out.reverse();
        out
    }

    fn handle_expr(&mut self, expr_id: ExprId) {
        let expr = &self.arena[expr_id];

        if let Expression::Ternary { .. } | Expression::LogicalOp { .. } = expr {
            // Don't recurse into ternaries: it'd be a) unsound because we'd inline across control
            // flow, b) slow because both the branches and the condition were populated from
            // an `if`, which we've already invoked `inline_expressions` on, and this would be the
            // second time. Same reasoning applies for logical operations.
            return;
        }

        let Expression::Variable(var) = *expr else {
            for sub_expr_id in expr.subexprs().rev() {
                self.handle_expr(sub_expr_id);
            }
            return;
        };

        if var.name.namespace == VariableNamespace::Slot {
            // Avoid inlining variable assignments present in source.
            return;
        }

        let n_mentions = *self
            .n_var_mentions
            .get(&var)
            .expect("used variable not mentioned");
        if var.name.namespace != VariableNamespace::Exception {
            // XXX: let's handle exceptions in some other manner...
            assert!(n_mentions > 1, "too low mention count");
        }

        // We can only inline a definition into a use if it's the only use capturing the definition.
        // XXX: There are minor exceptions to this rule, namely when we can insert the expressions
        // `var = expr`, `var++`, or `++var` to both commit an assignment and get a value.

        // Expect 2 mentions: a single definition and a single use.
        if n_mentions > 2 {
            return;
        }

        // We can't inline over side effects, but basically every statement might have a side
        // effect, so the most reasonable approach is to only inline consecutive statements. This
        // also allows us not to worry about inlining expressions across assignments to variables
        // that the expression might access.

        // Is the previous statement a definition of this variable?
        if let Some(stmt_meta) = self.rev_stmts.peek()
            && let Statement::Basic(BasicStatement::Assign { target, value }) = stmt_meta.stmt
            && let Expression::Variable(def_var) = self.arena[target]
            && def_var == var
        {
            // Commit to inlining. This removes the statement from the output.
            self.rev_stmts.next();

            // Inline recursively. We don't have to worry about `handle_expr` being called twice for
            // the value because its defining statement has just been dropped from iteration. See
            // the comment in `handle_stmt_list` for why we need to skip this if the assignment came
            // from the first statement.
            if self.rev_stmts.peek().is_some() {
                self.handle_expr(value);
            }

            // We can't modify `arena` here directly because there's an immutable reference to its
            // elements up the stack; delay it until later.
            self.inlined_exprs.push((expr_id, value));
        }
    }
}
