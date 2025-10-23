use crate::ast::{BasicStatement, Expression};
use crate::cfg::Statement;
use std::collections::HashMap;

// We could remove `block #n` altogether if there's also few breaks, but we might as well do that in
// another pass, as, chances are, there *are* breaks, they'll just become avoidable only after
// inlining, and we don't want to optimize out breaks from all over the place all the time, we'll do
// it just once afterwards.

struct LoopInfo {
    is_divergent: bool,
}

// Also removes redundant breaks and unused blocks. We can't remove redundant continues yet because
// continues can only be redundant in loops, not blocks, and at the point when we recurse into
// `block { .. }`, we don't yet know if we're going to lower it as `while { .. }` or
// `while { .. break; }`, so we have no idea whether `..` *will* fall through to break or continue.
fn make_loops<'a>(
    mut stmt: Statement<'a>,
    fallthrough_breaks_from: Option<usize>,
    out: &mut Vec<Statement<'a>>,
) -> LoopInfo {
    let info = match stmt {
        Statement::Basic(ref stmt) => LoopInfo {
            is_divergent: stmt.is_divergent(),
        },

        Statement::Block {
            id,
            ref mut children,
        } => {
            let mut info = make_loops_in_list(children, fallthrough_breaks_from.or(Some(id)));
            let mut children = core::mem::take(children);

            let (n_continues, n_breaks) = info.uses.take(id);

            if n_continues == 0 && n_breaks == 0 {
                out.extend(children);
                return info;
            }

            if let Some(Statement::If {
                then_children,
                else_children,
                ..
            }) = children.last()
                && let [
                    Statement::Continue {
                        block_id: continue_block_id,
                    },
                ] = **then_children
                && continue_block_id == id
                && else_children.is_empty()
                && n_continues == 1
            {
                let Some(Statement::If {
                    condition,
                    condition_inverted,
                    ..
                }) = children.pop()
                else {
                    unreachable!()
                };
                stmt = Statement::DoWhile {
                    id,
                    condition,
                    condition_inverted,
                    children,
                };
            } else if n_continues == 0 {
                stmt = Statement::DoWhile {
                    id,
                    condition: Box::new(Expression::ConstInt(0)),
                    condition_inverted: false,
                    children,
                };
            } else {
                if !info.is_divergent {
                    children.push(Statement::Break { block_id: id });
                }
                stmt = Statement::While {
                    id,
                    condition: Box::new(Expression::ConstInt(1)),
                    condition_inverted: false,
                    children,
                };
            }

            info
        }

        Statement::DoWhile { .. } => {
            panic!("do..while shouldn't have appeared in the AST at this pass");
        }

        Statement::While { .. } => panic!("while shouldn't have appeared in the AST at this pass"),

        Statement::If {
            ref mut then_children,
            ref mut else_children,
            ..
        } => {
            let then_info = make_loops_in_list(then_children, fallthrough_breaks_from);
            let else_info = make_loops_in_list(else_children, fallthrough_breaks_from);
            let mut uses = then_info.uses;
            uses.merge(else_info.uses);
            LoopInfo {
                uses,
                is_divergent: then_info.is_divergent && else_info.is_divergent,
            }
        }

        Statement::Switch {
            id, ref mut arms, ..
        } => {
            // Immediately remove arms equivalent to `break`, i.e. those starting with `break` or
            // empty ones eventually followed by `break`. These are usually just implicit
            // `default: break;` arms. Curiously, such arms don't have to be consecutive even though
            // they jump to the same statement, as these jumps may have been inlined from different
            // regions.
            let effective_block_id = fallthrough_breaks_from.unwrap_or(id);

            let mut filtered_arms: Vec<(Option<i32>, Vec<Statement<'_>>)> = Vec::new();
            for arm in core::mem::take(arms) {
                if let [Statement::Break { block_id }, ..] = *arm.1
                    && block_id == effective_block_id
                {
                    // Equivalent to break
                    while filtered_arms.pop_if(|arm| arm.1.is_empty()).is_some() {}
                    continue;
                }
                filtered_arms.push(arm);
            }
            while filtered_arms.pop_if(|arm| arm.1.is_empty()).is_some() {}
            *arms = filtered_arms;

            let mut uses = BlockUses::new();
            let n_arms = arms.len();
            let mut last_arm_is_divergent = false;
            let mut has_default_arm = false;
            for (i, (key, children)) in arms.iter_mut().enumerate() {
                let is_last_arm = i == n_arms - 1;
                // All remaining arms, except the last one, cannot fallthrough to `break`, as we've
                // just removed everything equivalent to `break`.
                let arm_info =
                    make_loops_in_list(children, is_last_arm.then_some(effective_block_id));
                uses.merge(arm_info.uses);
                last_arm_is_divergent = arm_info.is_divergent;
                if key.is_none() {
                    has_default_arm = true;
                }
            }

            let (n_continues, n_breaks) = uses.take(id);
            assert_eq!(n_continues, 0, "continue to switch");

            LoopInfo {
                uses,
                is_divergent: last_arm_is_divergent && n_breaks == 0 && has_default_arm,
            }
        }

        Statement::Continue { block_id } => LoopInfo { is_divergent: true },

        Statement::Break { block_id } => {
            if fallthrough_breaks_from == Some(block_id) {
                return LoopInfo {
                    is_divergent: false,
                };
            }
            LoopInfo { is_divergent: true }
        }
    };

    out.push(stmt);
    info
}

fn with_entry(
    map: &mut HashMap<usize, usize>,
    key: Option<usize>,
    value: usize,
    cb: impl FnOnce(&mut HashMap<usize, usize>),
) {
    // We could have a single match over `key`, but then `cb` would be called twice, either
    // inhibiting inlining or blowing up code size; I'd rather not do that.
    let old_value = if let Some(key) = key {
        map.insert(key, value)
    } else {
        None
    };
    cb(map);
    if let Some(key) = key {
        if let Some(old_value) = old_value {
            map.insert(key, old_value);
        } else {
            map.remove(&key);
        }
    }
}

// `continue`s can be no-ops and need to be removed, or they can `continue` from outer loops, where
// `break` from an inner loop would be equivalent. There's no need to redirect `break`s because they
// can never be equivalent post block-to-loop conversion. Also simplifies `if`s that now have empty
// `then`s.
fn simplify_continues(
    stmt: &mut Statement<'_>,
    fallthrough_continues_in: Option<usize>,
    // Mutable for optimization, but the logical value needs to be retained across the call (unless
    // the function panics)
    continue_to_break: &mut HashMap<usize, usize>,
) -> bool {
    match stmt {
        Statement::Basic(_) | Statement::Break { .. } => {}

        Statement::Block { .. } => panic!("block shouldn't have appeared in the AST at this pass"),

        Statement::DoWhile { id, children, .. } | Statement::While { id, children, .. } => {
            with_entry(
                continue_to_break,
                fallthrough_continues_in,
                *id,
                |continue_to_break| {
                    simplify_continues_in_list(children, Some(*id), continue_to_break);
                },
            );
        }

        Statement::If {
            then_children,
            else_children,
            condition_inverted,
            ..
        } => {
            simplify_continues_in_list(then_children, fallthrough_continues_in, continue_to_break);
            simplify_continues_in_list(else_children, fallthrough_continues_in, continue_to_break);
            if then_children.is_empty() && !else_children.is_empty() {
                core::mem::swap(then_children, else_children);
                *condition_inverted = !*condition_inverted;
            }
        }

        Statement::Switch { id, arms, .. } => {
            let n_arms = arms.len();
            for (i, (_, children)) in arms.iter_mut().enumerate() {
                with_entry(
                    continue_to_break,
                    fallthrough_continues_in,
                    *id,
                    |continue_to_break| {
                        simplify_continues_in_list(
                            children,
                            if i == n_arms - 1 {
                                fallthrough_continues_in
                            } else {
                                None
                            },
                            continue_to_break,
                        );
                    },
                );
            }
        }

        Statement::Continue { block_id } => {
            if fallthrough_continues_in == Some(*block_id) {
                return false;
            }
            if let Some(block_id) = continue_to_break.get(block_id) {
                *stmt = Statement::Break {
                    block_id: *block_id,
                };
            }
        }
    }

    true
}

fn simplify_continues_in_list(
    stmts: &mut Vec<Statement<'_>>,
    fallthrough_continues_in: Option<usize>,
    continue_to_break: &mut HashMap<usize, usize>,
) {
    let mut new_stmts = Vec::new();
    for i in 0..stmts.len() {
        let mut stmt =
            core::mem::replace(&mut stmts[i], Statement::Basic(BasicStatement::ReturnVoid));
        let should_retain = simplify_continues(
            &mut stmt,
            if i == stmts.len() - 1 {
                fallthrough_continues_in
            } else if let Statement::Continue { block_id } = stmts[i + 1] {
                // We only match a simple continue rather than blocks eventually containing continue
                // because there aren't any blocks anymore.
                Some(block_id)
            } else {
                None
            },
            continue_to_break,
        );
        if should_retain {
            new_stmts.push(stmt);
        }
    }
    *stmts = new_stmts;
}

pub fn rewrite_control_flow(stmts: &mut Vec<Statement<'_>>) {
    make_loops_in_list(stmts, None);
    simplify_continues_in_list(stmts, None, &mut HashMap::new());

    // The resulting code is mostly optimal with respect to non-inlined basic statements, with the
    // exceptions of:
    // a) `continue` inside `do`..`while` being cursed and simulated with a nested
    //    `do { .. } while (false);` because we don't yet know what the condition looks like,
    // b) Heuristics not having been applied yet wrt. the choice of nested `if`s vs
    //    `break`, and loops starting with `while { .. }` vs `.. if { continue }` or ending with
    //    `if { .. }` vs `if { continue } ..`.
}
