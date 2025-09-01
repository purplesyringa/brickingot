use super::{BasicBlock, Statement, abstract_eval::UnresolvedUse};
use crate::arena::{Arena, ExprId};
use crate::ast::{BasicStatement, Expression, Variable, VariableName, VariableNamespace};
use crate::dsu::DisjointSetUnion;
use rustc_hash::FxHashMap;
use std::collections::hash_map::Entry;

// We're interested in finding definitions of `name` matching the predicate, and we want them to be
// merged with `use_expr_id`.
struct UseDefTask {
    bb_id: usize,
    name: VariableName,
    use_expr_id: ExprId,
    predicate: Predicate,
}

enum Predicate {
    // Visible at the entry to `bb_id`.
    AtStart,
    // Visible at any point within `bb_id`.
    Within,
}

struct Merger<'a> {
    basic_blocks: &'a [BasicBlock],
    dsu: DisjointSetUnion,
    resolved_uses: FxHashMap<(usize, VariableName), ExprId>,
    tasks: Vec<UseDefTask>,
}

impl<'a> Merger<'a> {
    fn new(basic_blocks: &'a [BasicBlock], dsu_len: u32) -> Self {
        Self {
            basic_blocks,
            dsu: DisjointSetUnion::new(dsu_len),
            resolved_uses: FxHashMap::default(),
            tasks: Vec::new(),
        }
    }

    /// Merge all definitions of `name` visible at the start of `bb_id` with version `use_expr_id`.
    fn visit_use(&mut self, bb_id: usize, name: VariableName, use_expr_id: ExprId) {
        // Reuse single stack allocation between `visit_use` calls.
        self.tasks.push(UseDefTask {
            bb_id,
            name,
            use_expr_id,
            predicate: Predicate::AtStart,
        });

        while let Some(UseDefTask {
            bb_id,
            name,
            use_expr_id,
            predicate,
        }) = self.tasks.pop()
        {
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

            if let Predicate::Within = predicate {
                assert_eq!(
                    name.namespace,
                    VariableNamespace::Slot,
                    "can only recognize slot assignments for Within predicate",
                );
                if let Some(defs) = self.basic_blocks[bb_id].sealed_bb.slot_defs.get(&name) {
                    for def_expr_id in defs {
                        self.dsu.merge(use_expr_id.0, def_expr_id.0);
                    }
                }
            }

            if let Some(eh) = &self.basic_blocks[bb_id].eh {
                if name.namespace == VariableNamespace::Stack && name.id == 0 {
                    // This one's a bit weird -- we're merging ExprId's associated with different
                    // variable names. The point here is to merge all uses of a single exception0
                    // together. We couldn't care less about the version of exception0 itself: they
                    // may eventually even alias between basic blocks.
                    self.dsu.merge(use_expr_id.0, eh.unique_exception_expr_id.0);
                } else {
                    // Exception handlers can see `slotN` definitions from the throw site, but not
                    // `stackN` (since stack is cleared on entry) or `valueN` (since it can only be
                    // inlined across BBs due to stack reads).
                    assert_eq!(
                        name.namespace,
                        VariableNamespace::Slot,
                        "exception handler cannot capture {}",
                        name
                    );

                    // This includes even definitions that are overwritten by the end of the BB,
                    // since an exception may be thrown before the reassignment.
                    for pred_bb_id in &eh.throw_sites {
                        self.tasks.push(UseDefTask {
                            bb_id: *pred_bb_id,
                            name,
                            use_expr_id,
                            predicate: Predicate::Within,
                        });
                    }
                }
            }

            for pred_bb_id in &self.basic_blocks[bb_id].predecessors {
                if let Some(def) = self.basic_blocks[*pred_bb_id]
                    .sealed_bb
                    .active_defs_at_end
                    .get(&name)
                {
                    let def_expr_id = def.def_expr_id.expect("def_expr_id not set for variable");
                    self.dsu.merge(use_expr_id.0, def_expr_id.0);
                    if let Some(var) = def.copy_stack_from_predecessor {
                        // Now that we know the store is live, use what it loads from.
                        self.tasks.push(UseDefTask {
                            bb_id,
                            name: var.name,
                            use_expr_id: var.version,
                            predicate: Predicate::AtStart,
                        });
                    }
                } else {
                    self.tasks.push(UseDefTask {
                        bb_id: *pred_bb_id,
                        name,
                        use_expr_id,
                        predicate: Predicate::AtStart,
                    });
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

    // Remove dead stack stores, i.e. definitions that weren't merged with any use during DFS. This
    // is not the same thing as removing *post-optimization* dead stack stores, since this retains
    // used definitions even if all uses were replaced with values.
    statements.retain(|stmt| {
        if let Statement::Basic(BasicStatement::Assign { target, value }) = stmt
            && let Expression::Variable(Variable {
                name,
                version: def_expr_id,
            }) = arena[*target]
            && name.namespace == VariableNamespace::Stack
            && merger.is_unique(def_expr_id)
        {
            // `value` must be a `valueN` variable; remove it from the arena so that variable
            // refcounts can be computed just by iterating over the arena without recursion.
            // `high_level::main_opt` makes this assumption.
            arena[*value] = Expression::Null;

            false
        } else {
            true
        }
    });
}
