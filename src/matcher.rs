use crate::ast::{BasicStatement, Expression};
use crate::cfg::Statement;
use std::collections::HashMap;

struct BlockUses {
    // (continue, break)
    counters: HashMap<usize, (usize, usize)>,
}

impl BlockUses {
    fn new() -> Self {
        Self {
            counters: HashMap::new(),
        }
    }

    fn from_continue(block_id: usize) -> Self {
        Self {
            counters: core::iter::once((block_id, (1, 0))).collect(),
        }
    }

    fn from_break(block_id: usize) -> Self {
        Self {
            counters: core::iter::once((block_id, (0, 1))).collect(),
        }
    }

    fn merge(&mut self, mut rhs: BlockUses) {
        if self.counters.len() < rhs.counters.len() {
            // Small to large so that this is O(n log n) rather than quadratic
            core::mem::swap(self, &mut rhs);
        }
        for (key, source) in rhs.counters {
            let target = self.counters.entry(key).or_default();
            target.0 += source.0;
            target.1 += source.1;
        }
    }

    // Returns (continue, break)
    fn take(&mut self, key: usize) -> (usize, usize) {
        self.counters.remove(&key).unwrap_or_default()
    }
}

pub struct ConditionalInfo {
    // This doesn't cover bound blocks, i.e. blocks within the range.
    uses: BlockUses,
    is_divergent: bool,
    is_if_with_divergent_then: bool,
    first_unhandled_switch_arm_index: usize,
    n_breaks_from_switch: usize,
}

fn rewrite_conditionals_in_stmt(stmt: &mut Statement<'_>) -> ConditionalInfo {
    match stmt {
        Statement::Basic(stmt) => ConditionalInfo {
            uses: BlockUses::new(),
            is_divergent: stmt.is_divergent(),
            is_if_with_divergent_then: false,
            first_unhandled_switch_arm_index: 0,
            n_breaks_from_switch: 0,
        },

        Statement::Block { .. } => rewrite_conditionals_in_block(stmt),

        Statement::DoWhile { .. } => {
            panic!("do..while shouldn't have appeared in the AST at this pass");
        }

        Statement::While { .. } => panic!("while shouldn't have appeared in the AST at this pass"),

        Statement::If {
            then_children,
            else_children,
            ..
        } => {
            let mut uses = BlockUses::new();
            let mut last_then_stmt_is_divergent = false;
            let mut last_else_stmt_is_divergent = false;
            for (is_then, child) in core::iter::repeat(true)
                .zip(then_children)
                .chain(core::iter::repeat(false).zip(else_children))
            {
                let child_info = rewrite_conditionals_in_stmt(child);
                uses.merge(child_info.uses);
                if is_then {
                    last_then_stmt_is_divergent = child_info.is_divergent;
                } else {
                    last_else_stmt_is_divergent = child_info.is_divergent;
                }
            }
            ConditionalInfo {
                uses,
                is_divergent: last_then_stmt_is_divergent && last_else_stmt_is_divergent,
                is_if_with_divergent_then: last_then_stmt_is_divergent,
                first_unhandled_switch_arm_index: 0,
                n_breaks_from_switch: 0,
            }
        }

        Statement::Switch { id, arms, .. } => {
            let mut uses = BlockUses::new();
            let mut last_stmt_is_divergent = false;
            for (_, children) in arms {
                for child in children {
                    let child_info = rewrite_conditionals_in_stmt(child);
                    uses.merge(child_info.uses);
                    last_stmt_is_divergent = child_info.is_divergent;
                }
            }
            let n_breaks = uses.take(*id).1;
            let is_divergent = n_breaks == 0 && last_stmt_is_divergent;
            ConditionalInfo {
                uses,
                is_divergent,
                is_if_with_divergent_then: false,
                first_unhandled_switch_arm_index: 0,
                n_breaks_from_switch: n_breaks,
            }
        }

        Statement::Continue { block_id } => ConditionalInfo {
            uses: BlockUses::from_continue(*block_id),
            is_divergent: true,
            is_if_with_divergent_then: false,
            first_unhandled_switch_arm_index: 0,
            n_breaks_from_switch: 0,
        },

        Statement::Break { block_id } => ConditionalInfo {
            uses: BlockUses::from_break(*block_id),
            is_divergent: true,
            is_if_with_divergent_then: false,
            first_unhandled_switch_arm_index: 0,
            n_breaks_from_switch: 0,
        },
    }
}

fn rewrite_conditionals_in_block(stmt: &mut Statement<'_>) -> ConditionalInfo {
    let Statement::Block {
        id: block_id,
        ref mut children,
    } = *stmt
    else {
        unreachable!()
    };

    let mut uses = BlockUses::new();
    let mut first_switch_first_unhandled_switch_arm_index = 0;
    let mut first_switch_n_breaks_from_switch = 0;
    let mut last_stmt_is_divergent = false;
    let mut optimizable_ifs = Vec::new();
    for (i, child) in children.iter_mut().enumerate() {
        let child_info = rewrite_conditionals_in_stmt(child);
        uses.merge(child_info.uses);
        if i == 0 {
            first_switch_first_unhandled_switch_arm_index =
                child_info.first_unhandled_switch_arm_index;
            first_switch_n_breaks_from_switch = child_info.n_breaks_from_switch;
        }
        last_stmt_is_divergent = child_info.is_divergent;
        if child_info.is_if_with_divergent_then
            && let Statement::If { else_children, .. } = child
            && else_children.is_empty()
        {
            optimizable_ifs.push(i);
        }
    }

    let (n_continues, n_breaks) = uses.take(block_id);

    let mut info = ConditionalInfo {
        uses,
        is_divergent: last_stmt_is_divergent && n_breaks == 0,
        is_if_with_divergent_then: false,
        first_unhandled_switch_arm_index: 0,
        n_breaks_from_switch: 0,
    };

    // Current goal: reduce the necessity of this block by inlining statements into arms of `if`.
    //     block #n {
    //         if (cond1) { // trivial if example
    //             break #n;
    //         } else {}
    //         rest1;
    //         if (cond2) { // non-trivial if example
    //             body2; // diverging
    //         } else {}
    //         rest2;
    //         ...
    //         if (condk) {
    //             break #n;
    //         } else {}
    //         restk;
    //     } block #n
    // -> (if there's no `continue #n`, i.e if there's a chance that the block can be removed)
    //     block #n {
    //         if (!cond1) {
    //             rest1;
    //             if (cond2) {
    //                 body2;
    //             } else {
    //                 rest2;
    //                 ...
    //                 if (!condk) {
    //                     restk;
    //                 } else {}
    //             }
    //         } else {}
    //     }
    // If the first `if` was trivial, we then also swap around `block #n` and `if (!cond1)` blocks
    // so that the outer `if`'s `else` can be inlined into on the next iteration.
    //
    // We could remove `block #n` altogether if there's also few breaks, but we might as well do
    // that in another pass, as, chances are, there *are* breaks, they'll just become avoidable only
    // after inlining, and we don't want to optimized out breaks from all over the place all the
    // time, we'll do it just once afterwards.
    //
    // Although it may look like inlining into `else` increases code nesting without a benefit,
    // that's not the case: while an `if` statement is being parsed, `then` is *always* divergent,
    // even if it won't be after optimization:
    //     block #n {
    //         if (cond) {
    //             then;
    //             break #n;
    //         }
    //         else;
    //     }
    // -> (what we'll do in this pass)
    //     block #n {
    //         if (cond) {
    //             then;
    //             break #n;
    //         } else {
    //             else;
    //         }
    //     }
    // -> (what we'll optimize this to later on)
    //     if (cond) {
    //         then;
    //     } else {
    //         else;
    //     }
    //
    // If `optimizable_ifs` is non-empty, it provably includes 0 if the code is generated by cfg.
    if n_continues == 0 && optimizable_ifs.get(0) == Some(&0) {
        let mut first_if_is_trivial = false;

        for i in optimizable_ifs.into_iter().rev() {
            let rest: Vec<Statement<'_>> = children.drain(i + 1..).collect();
            let Some(Statement::If {
                condition_inverted,
                then_children,
                else_children,
                ..
            }) = children.last_mut()
            else {
                unreachable!()
            };
            let is_trivial = matches!(
                **then_children,
                [Statement::Break {
                    block_id: break_block_id,
                }] if break_block_id == block_id,
            );
            first_if_is_trivial = is_trivial;
            if is_trivial {
                *condition_inverted = !*condition_inverted;
                *then_children = rest;
            } else {
                *else_children = rest;
            }
        }

        if first_if_is_trivial {
            let Some(Statement::If {
                condition,
                condition_inverted,
                then_children,
                ..
            }) = children.pop()
            else {
                unreachable!()
            };
            *stmt = Statement::If {
                condition,
                condition_inverted,
                then_children: vec![Statement::Block {
                    id: block_id,
                    children: then_children,
                }],
                else_children: Vec::new(),
            };
            // `then` doesn't diverge if someone uses inside the `then` block still effectively uses
            // `break #n`.
            info.is_if_with_divergent_then = last_stmt_is_divergent && n_breaks == 1;
        }

        return info;
    }

    // Current goal: merge arms into `switch`.
    //     block #n {
    //         switch #m {
    //             ...
    //             case key1: ... case keyk: break #m;
    //             case nextkey: break #n; // or end of switch, or body is divergent
    //             ...
    //         }
    //         body;
    //     }
    // -> (if these are the only uses of `break #m`, and `continue #n` is absent)
    //     switch #n {
    //         ...
    //         case key1: ... case keyk: body;
    //         case nextkey: break #n;
    //         ...
    //     }
    // `switch` is not *guaranteed* to always be the first statement in the block, but it *is* in
    // any code generated by javac, mostly because javac lowers `switch { case: continue #n; }` as
    // a normal arm with a body of `continue #n`, rather than by making `continue #n` the target of
    // the switch instruction.
    if let Some(Statement::Switch {
        id: switch_id,
        arms,
        ..
    }) = children.get_mut(0)
        && n_continues == 0
    {
        // Nested blocks are supposed to have increasing block IDs, meaning that `break` targets are
        // supposed to be decreasing, so we can get linear runtime here at the cost of suboptimal
        // (but still correct) output on input not generated by cfg. Which shouldn't be problematic
        // in any way.

        let mut left = first_switch_first_unhandled_switch_arm_index; // that's a mouthful...
        while left < arms.len() {
            if let [Statement::Break {
                block_id: break_block_id,
            }] = *arms[left].1
                && break_block_id <= *switch_id
            {
                break;
            }
            left += 1;
        }

        let mut right = left;
        while right < arms.len()
            && let [Statement::Break {
                block_id: break_block_id,
            }] = *arms[right].1
            && break_block_id == *switch_id
        {
            right += 1;
        }

        let found_all_breaks = right - left == first_switch_n_breaks_from_switch;
        let fallthrough_equivalent_to_break = right == arms.len()
            || matches!(
                *arms[right].1,
                [Statement::Break {
                    block_id: break_block_id
                }] if break_block_id == block_id,
            )
            || last_stmt_is_divergent;

        if found_all_breaks && fallthrough_equivalent_to_break {
            let Statement::Switch { key, mut arms, .. } = children.remove(0) else {
                unreachable!()
            };

            // `left == right` can happen if a block wraps a switch, but the block is not otherwise
            // used.
            if left < right {
                for i in left..right - 1 {
                    arms[i].1.clear();
                }
                arms[right - 1].1 = core::mem::take(children);
            }

            *stmt = Statement::Switch {
                id: block_id,
                key,
                arms,
            };

            info.first_unhandled_switch_arm_index = right;
            info.n_breaks_from_switch = n_breaks;
        }
    }

    info
}

fn iterate_with_is_last<T>(vec: Vec<T>) -> impl Iterator<Item = (bool, T)> {
    let len = vec.len();
    vec.into_iter()
        .enumerate()
        .map(move |(i, element)| (i == len - 1, element))
}

struct LoopInfo {
    // This doesn't cover bound blocks, i.e. blocks within the range.
    uses: BlockUses,
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
            uses: BlockUses::new(),
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
                && let [Statement::Continue {
                    block_id: continue_block_id,
                }] = **then_children
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

        Statement::Continue { block_id } => LoopInfo {
            uses: BlockUses::from_continue(block_id),
            is_divergent: true,
        },

        Statement::Break { block_id } => {
            if fallthrough_breaks_from == Some(block_id) {
                return LoopInfo {
                    uses: BlockUses::new(),
                    is_divergent: false,
                };
            }
            LoopInfo {
                uses: BlockUses::from_break(block_id),
                is_divergent: true,
            }
        }
    };

    out.push(stmt);
    info
}

fn make_loops_in_list(
    stmts: &mut Vec<Statement<'_>>,
    fallthrough_breaks_from: Option<usize>,
) -> LoopInfo {
    let mut uses = BlockUses::new();
    let mut last_stmt_is_divergent = false;

    let mut new_stmts = Vec::new();
    for (is_last, stmt) in iterate_with_is_last(core::mem::take(stmts)) {
        let stmt_info = make_loops(
            stmt,
            if is_last {
                fallthrough_breaks_from
            } else {
                None
            },
            &mut new_stmts,
        );
        uses.merge(stmt_info.uses);
        last_stmt_is_divergent = stmt_info.is_divergent;
    }

    *stmts = new_stmts;

    LoopInfo {
        uses,
        is_divergent: last_stmt_is_divergent,
    }
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
    for stmt in &mut *stmts {
        rewrite_conditionals_in_stmt(stmt);
    }
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
