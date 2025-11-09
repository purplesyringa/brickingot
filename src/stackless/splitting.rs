// Merge versions of definitions with versions of uses that see those definitions.
//
// In a nutshell, this is implemented via DFS over vertices of kind `(bb_id, var)`, which should be
// read as "definitions of `var` visible at the beginning of `bb_id`" (the edges are generated to
// follow this rule). Each connected subgraph is essentially associated with a unique `version`
// computed with union-find.
//
// The worst-case time complexity is O(n_basic_blocks * n_variables), which is quadratic, just like
// linking. But since linking removes a lot of stack variables in favor of `valueN`, and this pass
// only merges `stackN` and `slotN` use-def chains, this is closer to O(n_basic_blocks * n_locals).
// While this can get quite large, it's reasonably fast in practice.

use super::{ExceptionHandlerBlock, InternalBasicBlock, Statement, abstract_eval::UnresolvedUse};
use crate::ast::{
    Arena, BasicStatement, Expression, Variable, VariableName, VariableNamespace, Version,
};
use crate::utils::UnionFind;
use crate::var;
use alloc::collections::BTreeMap;
use core::cell::Cell;
use rustc_hash::FxHashMap;
use std::collections::hash_map::Entry;

// We're interested in finding definitions of `name` matching the predicate, and we want them to be
// merged with `use_version`.
struct UseDefTask {
    bb_id: usize,
    name: VariableName,
    use_version: Version,
    predicate: Predicate,
}

enum Predicate {
    // Visible at the entry to `bb_id`.
    AtStart,
    // Visible at any point within `bb_id`.
    Within,
}

type TryRangeMap = BTreeMap<usize, (usize, Version)>; // start -> (end, use_version)

struct Merger<'a> {
    basic_blocks: &'a [InternalBasicBlock],
    versions: MergedVariables,
    resolved_uses: FxHashMap<(usize, VariableName), Version>, // (bb_id, name) -> version
    try_ranges_per_variable: FxHashMap<VariableName, TryRangeMap>,
    tasks: Vec<UseDefTask>,
}

impl<'a> Merger<'a> {
    fn new(basic_blocks: &'a mut [InternalBasicBlock], n_versions: u32) -> Self {
        Self {
            basic_blocks,
            versions: MergedVariables {
                versions: UnionFind::new(n_versions),
            },
            resolved_uses: FxHashMap::default(),
            try_ranges_per_variable: FxHashMap::default(),
            tasks: Vec::new(),
        }
    }

    /// Merge all definitions of `name` visible at the start of `bb_id` with version `use_version`.
    fn visit_use(&mut self, bb_id: usize, name: VariableName, use_version: Version) {
        // Reuse single stack allocation between `visit_use` calls.
        self.tasks.push(UseDefTask {
            bb_id,
            name,
            use_version,
            predicate: Predicate::AtStart,
        });

        while let Some(task) = self.tasks.pop() {
            self.handle_task(task);
        }
    }

    fn handle_task(&mut self, task: UseDefTask) {
        let UseDefTask {
            bb_id,
            name,
            use_version,
            predicate,
        } = task;

        // `resolved_uses` stores *some* valid representative of the connected component.
        match self.resolved_uses.entry((bb_id, name)) {
            Entry::Occupied(entry) => {
                self.versions.merge(use_version, *entry.get());
                return;
            }
            Entry::Vacant(entry) => {
                // DFS will merge all reachable definitions with `use_version`, so that's a valid
                // representative for all further iterations.
                entry.insert(use_version);
            }
        }

        if let Predicate::Within = predicate {
            assert_eq!(
                name.namespace,
                VariableNamespace::Slot,
                "can only recognize slot assignments for Within predicate",
            );
            if let Some(defs) = self.basic_blocks[bb_id].sealed_bb.slot_defs.get(&name) {
                for def_version in defs {
                    self.versions.merge(use_version, *def_version);
                }
            }
        }

        if let Some(eh) = &self.basic_blocks[bb_id].eh {
            self.handle_eh_task(name, use_version, eh);
        }

        for pred_bb_id in &self.basic_blocks[bb_id].predecessors {
            if let Some(def) = self.basic_blocks[*pred_bb_id]
                .sealed_bb
                .active_defs_at_end
                .get(&name)
            {
                let def_version = def.def_version.expect("def_version not set for variable");
                self.versions.merge(use_version, def_version);
                if let Some(var) = def.copy_stack_from_predecessor {
                    // Now that we know the store is live, use what it loads from.
                    self.tasks.push(UseDefTask {
                        bb_id,
                        name: var.name,
                        use_version: var.version,
                        predicate: Predicate::AtStart,
                    });
                }
            } else {
                self.tasks.push(UseDefTask {
                    bb_id: *pred_bb_id,
                    name,
                    use_version,
                    predicate: Predicate::AtStart,
                });
            }
        }
    }

    fn handle_eh_task(
        &mut self,
        name: VariableName,
        use_version: Version,
        eh: &ExceptionHandlerBlock,
    ) {
        if name == var!(stack0) {
            self.versions.merge(use_version, eh.stack_version);
            return;
        }

        // Exception handlers can see `slotN` definitions from the throw site, but not `stackN`
        // (since stack is cleared on entry) or `valueN` (since it can only be inlined across BBs
        // due to stack reads).
        assert_eq!(
            name.namespace,
            VariableNamespace::Slot,
            "exception handler cannot capture {}",
            name
        );

        // We want to merge `use_expr_id` with *all* definitions of the same variable within `try`
        // blocks that use this BB as the handler, since code may throw e.g. `VirtualMachineError`
        // at any point. In other words, we want to add a task for each BB contained within any
        // range in `eh_entry_for_bb_ranges`. But that would be superquadratic, so to preserve
        // reasonable time complexity, we maintain a per-variable auxiliary range map that contains
        // information about BB ranges that have already been handled.
        let map = self.try_ranges_per_variable.entry(name).or_default();

        for bb_range in &eh.eh_entry_for_bb_ranges {
            if bb_range.is_empty() {
                continue;
            }

            // Find and extract all ranges that intersect with `bb_range`.
            let it_start = map
                .range(..bb_range.start)
                .last()
                .map(|(start, _)| *start)
                .unwrap_or(0);
            let intersecting_ranges =
                map.extract_if(it_start..bb_range.end, |_, (end, _)| *end > bb_range.start);

            // Merge versions with intersecting ranges and get a list of uncovered ranges.
            let it_bb = Cell::new(bb_range.start);
            let mut new_range = bb_range.clone();
            let uncovered_ranges = intersecting_ranges
                .map(|(start, (end, range_expr_id))| {
                    new_range = new_range.start.min(start)..new_range.end.max(end);
                    let uncovered_range = it_bb.get()..start;
                    self.versions.merge(use_version, range_expr_id);
                    it_bb.set(end);
                    uncovered_range
                })
                .chain(core::iter::once_with(|| it_bb.get()..bb_range.end));

            // Add a task for each uncovered BB.
            for uncovered_bb_id in uncovered_ranges.flatten() {
                self.tasks.push(UseDefTask {
                    bb_id: uncovered_bb_id,
                    name,
                    use_version,
                    // We aren't merely looking for definitions live at the end of the BB, since
                    // an exception may be thrown before the reassignment, hence the predicate is
                    // "within".
                    predicate: Predicate::Within,
                });
            }

            // Mark the whole range as covered.
            assert!(
                map.insert(new_range.start, (new_range.end, use_version))
                    .is_none(),
                "corrupted range map",
            );
        }
    }

    fn finish(self) -> MergedVariables {
        self.versions
    }
}

struct MergedVariables {
    versions: UnionFind,
}

impl MergedVariables {
    fn merge(&mut self, a: Version, b: Version) {
        self.versions.merge(a.0, b.0)
    }

    fn resolve(&mut self, version: Version) -> Version {
        Version(self.versions.resolve(version.0))
    }

    fn is_unique(&self, version: Version) -> bool {
        self.versions.is_unique(version.0)
    }
}

pub fn merge_versions_across_basic_blocks(
    arena: &mut Arena<'_>,
    basic_blocks: &mut [InternalBasicBlock],
    unresolved_uses: &FxHashMap<(usize, Variable), UnresolvedUse>,
) {
    let mut merger = Merger::new(basic_blocks, arena.capacity());

    // Merge uses and definitions of `stackN` and `slotN` variables. We don't merge `valueN` here
    // because they all already share a version, and skipping value variables is just faster.
    for (&(bb_id, var), unresolved_use) in unresolved_uses {
        // We don't handle uses from possibly dead stores, but instead wait for the first live load
        // from the store.
        if !unresolved_use.is_stack_manipulation {
            merger.visit_use(bb_id, var.name, var.version);
        }
    }
    let mut merged = merger.finish();

    // Update all versions to the merged version. This iterates through possibly dead expressions,
    // but since `resolve` is infallible, it doesn't break anything.
    for expr in arena.iter_mut() {
        if let Expression::Variable(Variable { version, .. }) = expr {
            *version = merged.resolve(*version);
        }
    }

    for bb in basic_blocks {
        if let Some(eh) = &mut bb.eh {
            eh.stack_version = merged.resolve(eh.stack_version);
            // If the `stack0 = valueN` definition is directly used by anything and wasn't optimized
            // out during linking, it needs to be present in the resulting IR.
            eh.stack_value_copy_is_necessary = !merged.is_unique(eh.stack_version);
        }

        // Remove dead stack stores, i.e. stack definitions that weren't merged with any use during
        // DFS. This does not remove *all* dead stores, more specifically this leaves dead value
        // stores, but this still provides an important guarantee: all dead value stores are never
        // used.
        //
        // This is because `valueN` can ever be part of `valueM = expr` if `expr` is a non-trivial
        // computation, which we consider to be useful to retain even if it's pure. The only kinds
        // of trivial assignments loading values are `stackN = valueM`, which is guaranteed to be
        // live after this, and `slotN = valueM`, which is considered a side effect.
        //
        // This means that there can't be a chain of unused values holding each other hostage that
        // would require a DFS run to resolve, and instead we can just check whether a given
        // `valueN` variable is ever mentioned more than once to remove all dead stores. This allows
        // us to localize a heavy DFS step to this single pass and run much simpler logic to remove
        // `valueN` later.
        bb.sealed_bb.statements.retain(|stmt| {
            if let Statement::Basic(BasicStatement::Assign { target, value }) = stmt
                && let Expression::Variable(Variable { name, version }) = arena[*target]
                && name.namespace == VariableNamespace::Stack
                && merged.is_unique(version)
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
}
