use super::{BasicBlock, Statement, abstract_eval::UnresolvedUse};
use crate::arena::{Arena, ExprId};
use crate::ast::{BasicStatement, Expression, Variable, VariableName, VariableNamespace};
use crate::dsu::DisjointSetUnion;
use rustc_hash::FxHashMap;
use std::collections::hash_map::Entry;

struct Merger<'a> {
    basic_blocks: &'a [BasicBlock],
    dsu: DisjointSetUnion,
    resolved_uses: FxHashMap<(usize, VariableName), ExprId>,
    dfs_stack: Vec<(usize, VariableName, ExprId)>,
}

impl<'a> Merger<'a> {
    fn new(basic_blocks: &'a [BasicBlock], dsu_len: u32) -> Self {
        Self {
            basic_blocks,
            dsu: DisjointSetUnion::new(dsu_len),
            resolved_uses: FxHashMap::default(),
            dfs_stack: Vec::new(),
        }
    }

    /// Merge all definitions of `name` visible at the start of `bb_id` with version `use_expr_id`.
    fn visit_use(&mut self, bb_id: usize, name: VariableName, use_expr_id: ExprId) {
        // Reuse single stack allocation between `visit_use` calls.
        self.dfs_stack.push((bb_id, name, use_expr_id));
        while let Some((bb_id, name, use_expr_id)) = self.dfs_stack.pop() {
            // `resolved_uses` stores *some* valid representative of the connected component.
            match self.resolved_uses.entry((bb_id, name)) {
                Entry::Occupied(entry) => {
                    self.dsu.merge(use_expr_id.0, entry.get().0);
                    continue;
                }
                Entry::Vacant(entry) => {
                    // DFS will merge all reachable definitions with `use_expr_id`, so that's
                    // a valid representative for all further iterations.
                    entry.insert(use_expr_id);
                }
            }

            if name.namespace == VariableNamespace::Stack
                && name.id == 0
                && let Some(exception_expr_id) = self.basic_blocks[bb_id].unique_exception_expr_id
            {
                // This one's a bit weird -- we're merging ExprId's associated with different
                // variable names. The point here is to merge all uses of a single exception0
                // together. We couldn't care less about the version of exception0 itself: they may
                // eventually even alias between basic blocks.
                self.dsu.merge(use_expr_id.0, exception_expr_id.0);
            }

            for pred_bb_id in &self.basic_blocks[bb_id].predecessors {
                if let Some(def) = self.basic_blocks[*pred_bb_id].active_defs_at_end.get(&name) {
                    let def_expr_id = def.def_expr_id.expect("def_expr_id not set for variable");
                    self.dsu.merge(use_expr_id.0, def_expr_id.0);
                    if let Some(var) = def.copy_stack_from_predecessor {
                        // Now that we know the store is live, use what it loads from.
                        self.dfs_stack.push((bb_id, var.name, var.version));
                    }
                } else {
                    self.dfs_stack.push((*pred_bb_id, name, use_expr_id));
                }
            }
        }
    }

    fn resolve(&mut self, expr_id: ExprId) -> ExprId {
        ExprId(self.dsu.resolve(expr_id.0))
    }

    fn is_unique(&mut self, expr_id: ExprId) -> bool {
        self.dsu.is_unique(expr_id.0)
    }
}

pub fn merge_versions_across_basic_blocks(
    arena: &mut Arena<'_>,
    basic_blocks: &[BasicBlock],
    unresolved_uses: &FxHashMap<(usize, Variable), UnresolvedUse>,
    statements: &mut Vec<Statement>,
) {
    let mut merger = Merger::new(basic_blocks, arena.capacity());

    for (&(bb_id, var), unresolved_use) in unresolved_uses {
        // We don't handle uses from possibly dead stores, but instead wait for the first live load
        // from the store.
        if !unresolved_use.is_stack_manipulation {
            merger.visit_use(bb_id, var.name, var.version);
        }
    }

    // This iterates through possibly dead expressions, but since `resolve` is infallible, it
    // doesn't break anything.
    for expr in arena.iter_mut() {
        if let Expression::Variable(Variable { version, .. }) = expr {
            *version = merger.resolve(*version);
        }
    }

    // Remove dead stack stores, i.e. definitions that weren't merged with any use during DFS.
    statements.retain(|stmt| {
        if let Statement::Basic(BasicStatement::Assign { target, .. }) = stmt
            && let Expression::Variable(Variable {
                name,
                version: def_expr_id,
            }) = arena[*target]
            && name.namespace == VariableNamespace::Stack
            && merger.is_unique(def_expr_id)
        {
            false
        } else {
            true
        }
    });
}
