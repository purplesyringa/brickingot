use crate::arena::{Arena, ExprId};
use crate::ast::{Expression, Variable, VariableName, VariableNamespace};
use crate::stackless::BasicBlock;
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Clone, Copy, PartialEq)]
enum Source {
    Value { name: VariableName, bb_id: usize },
    ActiveException,
}

pub fn link_stack_across_basic_blocks(
    arena: &mut Arena<'_>,
    basic_blocks: &[BasicBlock],
    unresolved_uses: &FxHashMap<(usize, VariableName), Vec<ExprId>>,
) {
    // Resolve cross-BB stack uses to values, if those can be selected unambiguously and soundly.
    // Otherwise, keep the variable as-is.
    //
    // This can lead to suboptimal codegen in cases where the value is produced by a ternary
    // operator and then explicitly moved around the stack before being consumed, but javac never
    // emits such bytecode. This can theoretically be fixed at some performance cost, but is
    // probably unnecessary.
    //
    // The core of the algorithm is DFS over nodes `(bb_id, N)`, which denotes that we're
    // interested in what `stackN` might be equal to at the entry to `bb_id`. The worst-case time
    // complexity is O(n_basic_blocks * n_variables), making this one of the only quadratic
    // algorithms in the decompiler. However, this complexity is only reached when a significant
    // number of stack elements are held over a significant amount of basic blocks, which basically
    // only happens when a ton of ternaries are stuck together. This is so rare that this pass is,
    // in practice, instantaneous.

    let mut dfs_stack = Vec::new();
    let mut in_stack = FxHashSet::default();

    'uses: for (&(bb_id, name), uses) in unresolved_uses {
        if name.namespace != VariableNamespace::Stack {
            continue;
        }

        let mut source: Option<Source> = None;

        dfs_stack.clear();
        dfs_stack.push((bb_id, name.id));
        in_stack.clear();
        in_stack.insert((bb_id, name.id));
        while let Some((bb_id, position)) = dfs_stack.pop() {
            let mut try_push = |node| {
                // We can just skip nodes that we've already visited because we'll enumerate all
                // paths regardless.
                if in_stack.insert(node) {
                    dfs_stack.push(node);
                }
            };

            let name = VariableName {
                namespace: VariableNamespace::Stack,
                id: position,
            };

            // Find all assignments to `stackN` reachable from the beginning of `bb_id`.
            if position == 0 && basic_blocks[bb_id].is_exception_handler {
                if let Some(old_source) = source.replace(Source::ActiveException)
                    && old_source != Source::ActiveException
                {
                    continue 'uses;
                }
            }

            for pred_bb_id in &basic_blocks[bb_id].predecessors {
                if let Some(def) = basic_blocks[*pred_bb_id].active_defs_at_end.get(&name) {
                    if let Some(position) = def.copy_stack_from_predecessor {
                        try_push((*pred_bb_id, position));
                    } else {
                        assert!(
                            def.var.name.namespace == VariableNamespace::Value,
                            "invalid assignment {} = {}",
                            name,
                            def.var,
                        );
                        let new_source = Source::Value {
                            name: def.var.name,
                            bb_id: *pred_bb_id,
                        };
                        if let Some(old_source) = source.replace(new_source)
                            && old_source != new_source
                        {
                            continue 'uses;
                        }
                    }
                } else {
                    try_push((*pred_bb_id, position));
                }
            }
        }

        // This should never fail. We only run this pass on reachable code, so there's an execution
        // that reaches this statement. By retroactively tracking the source of the value in
        // `stackN`, we'll either stumble upon `valueM`, upon an exception handler, or upon
        // an uninitialized read from stack; but everything on the stack is always a valid value.
        let source = source.expect("stack variable without value initializer");

        if let Source::Value { bb_id, .. } = source {
            // Verify that `value` is not reassigned between the various definitions
            // `stackM = value` and the eventual use `stackN`. This is equivalent to verifying that
            // DFS has never entered the block defining `value`.
            //
            // Note that this will cause a "false" positive if the use and the `value` definition
            // are in the same BB, and the `value` is defined after the use. However, such use would
            // not have been resolved to `value` anyway, because `stackN` must have been populated
            // from a different source on the first entry to the BB.
            if in_stack.iter().any(|(it_bb_id, _)| *it_bb_id == bb_id) {
                continue 'uses;
            }
        }

        for use_expr_id in uses {
            // Strictly speaking, we've found a `value` that is valid at the entry to `bb_id`, not
            // at the exact location of the use. However, `value` could not have been reassigned
            // within this basic block because we've verified that DFS has not visited this BB.
            arena[*use_expr_id] = match source {
                Source::Value { name, .. } => Expression::Variable(Variable {
                    name,
                    version: *use_expr_id,
                }),
                Source::ActiveException => Expression::ActiveException,
            };
        }
    }
}
