use crate::ast::BasicStatement;
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

pub struct CodeInfo {
    // This doesn't cover bound blocks, i.e. blocks within the range.
    uses_by_block_id: BlockUses,
    is_divergent: bool,
    is_if_with_divergent_then: bool,
    first_unhandled_switch_arm_index: usize,
    n_breaks_from_switch: usize,
}

fn rewrite_conditionals_in_stmt(stmt: &mut Statement<'_>) -> CodeInfo {
    match stmt {
        Statement::Basic(stmt) => CodeInfo {
            uses_by_block_id: BlockUses::new(),
            is_divergent: match stmt {
                BasicStatement::Assign { .. }
                | BasicStatement::Calculate(_)
                | BasicStatement::MonitorEnter { .. }
                | BasicStatement::MonitorExit { .. } => false,
                BasicStatement::Return { .. }
                | BasicStatement::ReturnVoid
                | BasicStatement::Throw { .. } => true,
            },
            is_if_with_divergent_then: false,
            first_unhandled_switch_arm_index: 0,
            n_breaks_from_switch: 0,
        },

        Statement::Block { .. } => rewrite_conditionals_in_block(stmt),

        Statement::If {
            then_children,
            else_children,
            ..
        } => {
            let mut uses_by_block_id = BlockUses::new();
            let mut last_then_stmt_is_divergent = false;
            let mut last_else_stmt_is_divergent = false;
            for (is_then, child) in core::iter::repeat(true)
                .zip(then_children)
                .chain(core::iter::repeat(false).zip(else_children))
            {
                let child_info = rewrite_conditionals_in_stmt(child);
                uses_by_block_id.merge(child_info.uses_by_block_id);
                if is_then {
                    last_then_stmt_is_divergent = child_info.is_divergent;
                } else {
                    last_else_stmt_is_divergent = child_info.is_divergent;
                }
            }
            CodeInfo {
                uses_by_block_id,
                is_divergent: last_then_stmt_is_divergent && last_else_stmt_is_divergent,
                is_if_with_divergent_then: last_then_stmt_is_divergent,
                first_unhandled_switch_arm_index: 0,
                n_breaks_from_switch: 0,
            }
        }

        Statement::Switch { id, arms, .. } => {
            let mut uses_by_block_id = BlockUses::new();
            let mut last_stmt_is_divergent = false;
            for (_, children) in arms {
                for child in children {
                    let child_info = rewrite_conditionals_in_stmt(child);
                    uses_by_block_id.merge(child_info.uses_by_block_id);
                    last_stmt_is_divergent = child_info.is_divergent;
                }
            }
            let n_breaks = uses_by_block_id.take(*id).1;
            let is_divergent = n_breaks == 0 && last_stmt_is_divergent;
            CodeInfo {
                uses_by_block_id,
                is_divergent,
                is_if_with_divergent_then: false,
                first_unhandled_switch_arm_index: 0,
                n_breaks_from_switch: n_breaks,
            }
        }

        Statement::Continue { block_id } => CodeInfo {
            uses_by_block_id: BlockUses::from_continue(*block_id),
            is_divergent: true,
            is_if_with_divergent_then: false,
            first_unhandled_switch_arm_index: 0,
            n_breaks_from_switch: 0,
        },

        Statement::Break { block_id } => CodeInfo {
            uses_by_block_id: BlockUses::from_break(*block_id),
            is_divergent: true,
            is_if_with_divergent_then: false,
            first_unhandled_switch_arm_index: 0,
            n_breaks_from_switch: 0,
        },
    }
}

fn rewrite_conditionals_in_block(stmt: &mut Statement<'_>) -> CodeInfo {
    let Statement::Block {
        id: block_id,
        ref mut children,
    } = *stmt
    else {
        unreachable!()
    };

    let mut uses_by_block_id = BlockUses::new();
    let mut first_switch_first_unhandled_switch_arm_index = 0;
    let mut first_switch_n_breaks_from_switch = 0;
    let mut last_stmt_is_divergent = false;
    let mut optimizable_ifs = Vec::new();
    for (i, child) in children.iter_mut().enumerate() {
        let child_info = rewrite_conditionals_in_stmt(child);
        uses_by_block_id.merge(child_info.uses_by_block_id);
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

    let (n_continues, n_breaks) = uses_by_block_id.take(block_id);

    let mut code_info = CodeInfo {
        uses_by_block_id,
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
    // If `optimizable_ifs` is non-empty, it provably includes 0 if the code is generated by cfg.
    if n_continues == 0 && optimizable_ifs.get(0) == Some(&0) {
        let mut first_if_is_trivial = false;
        let mut n_trivial_ifs = 0;

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
                n_trivial_ifs += 1;
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
            assert!(n_breaks >= n_trivial_ifs, "too few breaks");
            code_info.is_if_with_divergent_then =
                last_stmt_is_divergent && n_breaks == n_trivial_ifs;
        }

        return code_info;
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

            code_info.first_unhandled_switch_arm_index = right;
            code_info.n_breaks_from_switch = n_breaks;
        }
    }

    /*
    // Build `do..while`:
    //     block #n {
    //         body;
    //         if (cond) {
    //         } else {
    //             continue #n;
    //         }
    //     }
    // ->
    //     do #n {
    //         body;
    //     } while (!cond); #n
    // as long as there's no `continue #n;` within `body`. `break #n;` is fine.
    if let Statement::Block { id, children } = stmt
        && let Some(Statement::If {
            then_children,
            else_children,
            ..
        }) = children.last()
        && then_children.is_empty()
        && let [Statement::Continue { block_id }] = **else_children
        && block_id == *id
        && block_uses.count_continue(*id) == 1
    {
        let Statement::If {
            condition,
            condition_inverted,
            ..
        } = children.pop().unwrap()
        else {
            unreachable!()
        };
        block_uses.remove_continue(block_id);
        *stmt = Statement::DoWhile {
            id: *id,
            children: core::mem::take(children),
            condition,
            condition_inverted: !condition_inverted,
        };
    }
    */

    code_info
}

fn iterate_with_is_last<T>(vec: Vec<T>) -> impl Iterator<Item = (bool, T)> {
    let len = vec.len();
    vec.into_iter()
        .enumerate()
        .map(move |(i, element)| (i == len - 1, element))
}

// Also removes redundant breaks and unused blocks
fn remove_breaks_and_blocks<'a>(
    mut stmt: Statement<'a>,
    fallthrough_breaks_from: Option<usize>,
    out: &mut Vec<Statement<'a>>,
) -> BlockUses {
    let uses = match stmt {
        Statement::Basic(_) => BlockUses::new(),

        Statement::Block {
            id,
            ref mut children,
        } => {
            let mut uses =
                remove_breaks_and_blocks_in_list(children, fallthrough_breaks_from.or(Some(id)));
            if uses.take(id) == (0, 0) {
                out.extend(core::mem::take(children));
                return uses;
            }
            uses
        }

        Statement::If {
            ref mut then_children,
            ref mut else_children,
            ..
        } => {
            let mut uses = remove_breaks_and_blocks_in_list(then_children, fallthrough_breaks_from);
            uses.merge(remove_breaks_and_blocks_in_list(
                else_children,
                fallthrough_breaks_from,
            ));
            uses
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
            for (i, (_, children)) in arms.iter_mut().enumerate() {
                let is_last_arm = i == n_arms - 1;
                uses.merge(remove_breaks_and_blocks_in_list(
                    children,
                    is_last_arm.then_some(effective_block_id),
                ));
            }

            uses.take(id); // not necessary, but helps clean up the data flow a bit

            uses
        }

        Statement::Continue { block_id } => BlockUses::from_continue(block_id),

        Statement::Break { block_id } => {
            if fallthrough_breaks_from == Some(block_id) {
                return BlockUses::new();
            }
            BlockUses::from_break(block_id)
        }
    };

    out.push(stmt);
    uses
}

fn remove_breaks_and_blocks_in_list(
    stmts: &mut Vec<Statement<'_>>,
    fallthrough_breaks_from: Option<usize>,
) -> BlockUses {
    let mut uses = BlockUses::new();
    let mut new_stmts = Vec::new();
    for (is_last, stmt) in iterate_with_is_last(core::mem::take(stmts)) {
        uses.merge(remove_breaks_and_blocks(
            stmt,
            if is_last {
                fallthrough_breaks_from
            } else {
                None
            },
            &mut new_stmts,
        ));
    }
    *stmts = new_stmts;
    uses
}

pub fn rewrite_control_flow(stmts: &mut Vec<Statement<'_>>) {
    for stmt in &mut *stmts {
        rewrite_conditionals_in_stmt(stmt);
    }
    remove_breaks_and_blocks_in_list(stmts, None);

    // TODO:
    // All blocks left need to be transformed to loops -- that can cover `do`..`while` and leave
    // everything else as plain `while (true)`. No plain blocks should be left after that.
}
