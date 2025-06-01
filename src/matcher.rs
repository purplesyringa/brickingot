use crate::cfg::Statement;
use std::collections::HashMap;

pub struct BlockUses {
    // `(break, continue)` counts
    counts_by_block_id: HashMap<usize, (usize, usize)>,
}

impl BlockUses {
    fn new() -> Self {
        Self {
            counts_by_block_id: HashMap::new(),
        }
    }

    fn merge(&mut self, mut rhs: BlockUses) {
        if self.counts_by_block_id.len() < rhs.counts_by_block_id.len() {
            // Small to large so that this is O(n log n) rather than quadratic
            core::mem::swap(self, &mut rhs);
        }
        for (block_id, (break_cnt, continue_cnt)) in rhs.counts_by_block_id {
            let entry = self.counts_by_block_id.entry(block_id).or_default();
            entry.0 += break_cnt;
            entry.1 += continue_cnt;
        }
    }

    fn add_break(&mut self, block_id: usize) {
        self.counts_by_block_id.entry(block_id).or_default().0 += 1;
    }

    fn add_continue(&mut self, block_id: usize) {
        self.counts_by_block_id.entry(block_id).or_default().1 += 1;
    }

    fn remove_break(&mut self, block_id: usize) {
        self.counts_by_block_id.get_mut(&block_id).unwrap().0 -= 1;
    }

    fn remove_continue(&mut self, block_id: usize) {
        self.counts_by_block_id.get_mut(&block_id).unwrap().1 -= 1;
    }

    fn count_break(&mut self, block_id: usize) -> usize {
        self.counts_by_block_id
            .get(&block_id)
            .copied()
            .unwrap_or_default()
            .0
    }

    fn count_continue(&mut self, block_id: usize) -> usize {
        self.counts_by_block_id
            .get(&block_id)
            .copied()
            .unwrap_or_default()
            .1
    }

    fn has_uses(&mut self, block_id: usize) -> bool {
        !matches!(self.counts_by_block_id.get(&block_id), None | Some((0, 0)))
    }
}

pub fn rewrite_control_flow(stmt: &mut Statement<'_>) -> BlockUses {
    // Rewrite chidren and compute block use information so that we can remove unused blocks during
    // certain rewrites.
    let mut block_uses = BlockUses::new();
    return block_uses;
    match stmt {
        Statement::Continue { block_id } => block_uses.add_continue(*block_id),
        Statement::Break { block_id } => block_uses.add_break(*block_id),
        _ => {}
    }
    for child in stmt.all_children_mut() {
        block_uses.merge(rewrite_control_flow(child));
    }

    // Inline into `if`:
    //     block #n {
    //         if (cond) {
    //         } else {
    //             break #n;
    //         }
    //         body;
    //     } block #n
    // ->
    //     block #n {
    //         if (cond) {
    //             body;
    //         } else {}
    //     }
    // -> (if #n is now unused)
    //     if (cond) {
    //         body;
    //     } else {}
    if let Statement::Block { id, children } = stmt
        && let Some(Statement::If {
            then_children,
            else_children,
            ..
        }) = children.get(0)
        && then_children.is_empty()
        && let [Statement::Break { block_id }] = **else_children
        && block_id == *id
    {
        let Statement::If {
            condition,
            condition_inverted,
            ..
        } = children.remove(0)
        else {
            unreachable!()
        };
        let if_stmt = Statement::If {
            condition,
            condition_inverted,
            then_children: core::mem::take(children),
            else_children: Vec::new(),
        };
        block_uses.remove_break(*id);
        *stmt = if block_uses.has_uses(*id) {
            Statement::Block {
                id: *id,
                children: vec![if_stmt],
            }
        } else {
            if_stmt
        };
    }

    // Inline into `else`:
    //     block #n {
    //         if (cond) {
    //             then_body;
    //             break #n;
    //         } else {
    //         }
    //         else_body;
    //     } block #n
    // ->
    //     block #n {
    //         if (cond) {
    //             then_body;
    //         } else {
    //             else_body;
    //         }
    //     } block #n
    // -> (if #n is now unused)
    //     if (cond) {
    //         then_body;
    //     } else {
    //         else_body;
    //     }
    if let Statement::Block { id, children } = stmt
        && let Some(Statement::If {
            then_children,
            else_children,
            ..
        }) = children.get(0)
        && else_children.is_empty()
        && let Some(Statement::Break { block_id }) = then_children.last()
        && block_id == id
    {
        let Statement::If {
            condition,
            condition_inverted,
            mut then_children,
            ..
        } = children.remove(0)
        else {
            unreachable!()
        };
        then_children.pop();
        let if_stmt = Statement::If {
            condition,
            condition_inverted,
            then_children,
            else_children: core::mem::take(children),
        };
        block_uses.remove_break(*id);
        *stmt = if block_uses.has_uses(*id) {
            Statement::Block {
                id: *id,
                children: vec![if_stmt],
            }
        } else {
            if_stmt
        };
    }

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

    block_uses
}
