// Resolve cross-BB stack uses to values, if those can be selected unambiguously and soundly.
// Otherwise, keep the variable as-is.
//
// This can lead to suboptimal codegen in cases where the value is produced by a ternary operator
// and then explicitly moved around the stack across multiple basic blocks before being consumed,
// but javac never emits such bytecode. This can theoretically be fixed at some performance cost,
// but is probably unnecessary.
//
// The core of the algorithm is DFS over nodes `(bb_id, N)`, which denotes that we're interested in
// what value `stackN` might be equal to at the entry to `bb_id`. Edges represent that information
// needs to be integrated from another node.
//
// Such graph has a worst-case size of O(n_basic_blocks * n_variables), making this one of the only
// quadratic pieces of the decompiler. This complexity is only reached when a significant number of
// stack elements are held over a significant amount of basic blocks, which basically only happens
// when a ton of ternaries are stuck together. This is so rare that the graph is, in practice, tiny.
//
// There's a tiny problem with SCCs -- during DFS, vertices that aren't entries to an SCC may
// contain information that doesn't include values reachable from the entire SCC, and that's
// an issue because we run DFS multiple times, one per unresolved use. This is fixed by locating
// SCCs with Tarjan's algorithm and propagating the up-to-date information.

use crate::abstract_eval::UnresolvedUse;
use crate::arena::Arena;
use crate::ast::{Expression, Variable, VariableName, VariableNamespace};
use crate::stackless::BasicBlock;
use rustc_hash::FxHashMap;
use std::collections::hash_map::Entry;

#[derive(Clone, Copy, PartialEq)]
enum Source {
    Value { var: Variable, def_bb_id: usize },
    ActiveException,
    Missing,
    Indeterminate,
}

impl Source {
    fn merge(&mut self, other: Source) {
        if let Source::Missing = other {
            return;
        }
        if let Source::Missing = self {
            *self = other;
            return;
        }
        if *self != other {
            *self = Source::Indeterminate;
        }
    }
}

#[derive(Clone, Copy)]
struct DfsNodeState {
    low_link: usize,
    source: Source,
}

struct Linker<'a> {
    basic_blocks: &'a [BasicBlock],
    node_info: FxHashMap<(usize, usize), DfsNodeState>,
    tarjan_stack: Vec<(usize, usize)>,
}

impl<'a> Linker<'a> {
    fn new(basic_blocks: &'a [BasicBlock]) -> Self {
        Self {
            basic_blocks,
            node_info: FxHashMap::default(),
            tarjan_stack: Vec::new(),
        }
    }

    fn visit(&mut self, node: (usize, usize)) -> DfsNodeState {
        let index = self.tarjan_stack.len();

        let mut state = match self.node_info.entry(node) {
            Entry::Occupied(entry) => return *entry.get(),
            Entry::Vacant(entry) => *entry.insert(DfsNodeState {
                low_link: index,
                source: Source::Missing,
            }),
        };

        self.tarjan_stack.push(node);

        let (bb_id, position) = node;

        let name = VariableName {
            namespace: VariableNamespace::Stack,
            id: position,
        };

        // Find all assignments to `stackN` reachable from the beginning of `bb_id`.
        if position == 0 && self.basic_blocks[bb_id].is_exception_handler {
            state.source.merge(Source::ActiveException);
        }

        for pred_bb_id in &self.basic_blocks[bb_id].predecessors {
            let next_node =
                if let Some(def) = self.basic_blocks[*pred_bb_id].active_defs_at_end.get(&name) {
                    if let Some(var) = def.copy_stack_from_predecessor {
                        (*pred_bb_id, var.name.id)
                    } else {
                        assert!(
                            def.var.name.namespace == VariableNamespace::Value,
                            "invalid assignment {} = {}",
                            name,
                            def.var,
                        );
                        state.source.merge(Source::Value {
                            var: def.var,
                            def_bb_id: *pred_bb_id,
                        });
                        continue;
                    }
                } else {
                    (*pred_bb_id, position)
                };

            let next_state = self.visit(next_node);
            state.source.merge(next_state.source);
            state.low_link = state.low_link.min(next_state.low_link);
        }

        let is_scc_root = state.low_link == index;
        if is_scc_root {
            if let Source::Missing = state.source {
                // This should be unreachable. We only run this pass on reachable code, so there's
                // an execution that reaches this statement. By retroactively tracking the source of
                // the value in `stackN`, we'll either stumble upon `valueM`, upon an exception
                // handler, or upon an uninitialized read from stack; but everything on the stack is
                // always a valid value.
                panic!("stack variable without value initializer");
            }

            for scc_node in self.tarjan_stack.drain(index..) {
                *self.node_info.get_mut(&scc_node).unwrap() = DfsNodeState {
                    low_link: usize::MAX,
                    source: state.source,
                };
            }
        } else {
            *self.node_info.get_mut(&node).unwrap() = state;
        }

        state
    }
}

pub fn link_stack_across_basic_blocks(
    arena: &mut Arena<'_>,
    basic_blocks: &[BasicBlock],
    unresolved_uses: &FxHashMap<(usize, Variable), UnresolvedUse>,
) {
    let mut linker = Linker::new(basic_blocks);

    for &(bb_id, var) in unresolved_uses.keys() {
        if var.name.namespace != VariableNamespace::Stack {
            continue;
        }

        let DfsNodeState { source, .. } = linker.visit((bb_id, var.name.id));
        assert!(linker.tarjan_stack.is_empty());

        match source {
            Source::Value { .. } | Source::ActiveException => {}
            Source::Missing => unreachable!(),
            Source::Indeterminate => continue,
        }

        // Suppose that `stack1` could only be populated from a single `value0`. That doesn't,
        // however, clearly imply that `stack1` equals the contents of `value0` *at time of use*.
        // Specifically, the concern is that a program execution with the following subsequence
        // could exist:
        //     value0 <- ...
        //     [eventually move value0 to stack0, perhaps via multiple copies]
        //     [the above may repeat several times]
        //     value0 <- ...
        //     [eventually move stack0 to stack1, perhaps via multiple copies]
        //     f(stack1)
        // Consider the path in the control flow graph this execution takes. Collapsing the part of
        // the path between the first `value0 <- ...` and the last `value0 <- ...` before
        // `f(stack1)` produces a different valid control flow path with the following semantics:
        //     value0 <- ...
        //     [eventually move stack0 to stack1, perhaps via multiple copies]
        //     f(stack1)
        // In this execution, `value0` has not been saved to `stack0`, and so `stack0` must have
        // been produced by something other than `value0`. Therefore, `value0` cannot be the only
        // source of `stack1`, and so the concern is irrelevant.

        arena[var.version] = match source {
            Source::Value { var, .. } => Expression::Variable(var),
            Source::ActiveException => Expression::ActiveException,
            _ => unreachable!(),
        };
    }
}
