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
// There's a small problem with using DFS on cyclic graphs: not all vertices in an SCCs will contain
// information about the entire SCC, since we don't visit nodes recursively multiple times. This is
// fixed by locating SCCs with Tarjan's algorithm and propagating the up-to-date information from
// the entry vertex to the whole SCC.

use super::{BasicBlock, abstract_eval::UnresolvedUse};
use crate::arena::Arena;
use crate::ast::{Expression, Variable, VariableName, VariableNamespace};
use rustc_hash::FxHashMap;
use std::collections::hash_map::Entry;

#[derive(Clone, Copy, Debug, PartialEq)]
enum Source {
    Value(Variable),
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

        // We need to worry about implicit assignment to `stack0` at EH entry, but not about
        // retaining any other variables on EH entry.
        if position == 0
            && let Some(eh) = &self.basic_blocks[bb_id].eh
        {
            state.source.merge(Source::Value(Variable {
                name: VariableName {
                    namespace: VariableNamespace::Exception,
                    id: 0,
                },
                version: eh.exception0_use,
            }));
        }

        for pred_bb_id in &self.basic_blocks[bb_id].predecessors {
            let next_node = if let Some(def) = self.basic_blocks[*pred_bb_id]
                .sealed_bb
                .active_defs_at_end
                .get(&name)
            {
                if let Some(var) = def.copy_stack_from_predecessor {
                    (*pred_bb_id, var.name.id)
                } else {
                    assert!(
                        def.var.name.namespace == VariableNamespace::Value,
                        "invalid assignment {} = {}",
                        name,
                        def.var,
                    );
                    state.source.merge(Source::Value(def.var));
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
    unresolved_uses: &mut FxHashMap<(usize, Variable), UnresolvedUse>,
) {
    let mut linker = Linker::new(basic_blocks);

    unresolved_uses.retain(|&(bb_id, var), _| {
        if var.name.namespace != VariableNamespace::Stack {
            return true;
        }

        let DfsNodeState { source, .. } = linker.visit((bb_id, var.name.id));
        assert!(linker.tarjan_stack.is_empty());

        // Suppose that `stack1` could only be populated from a single `value0`. That doesn't,
        // however, clearly imply that `stack1` equals the contents of `value0` *at time of use*,
        // i.e. that another store to `value0` hasn't occured.
        //
        // Specifically, the concern is that a program execution with the following subsequence of
        // statements could exist:
        //     value0 <- ...
        //     [eventually move value0 to stack0, perhaps via multiple copies]
        //     [the above may repeat several times]
        //     value0 <- ...
        //     [eventually move stack0 to stack1, perhaps via multiple copies]
        //     f(stack1) // populated from value0, but not from the latest store to value0!
        //
        // Consider the path in the control flow graph this execution takes. Collapse the part of
        // the path between the first store `value0 <- ...` in program order and the last store
        // `value0 <- ...` before the call `f(stack1)`. This produces a different, statically valid
        // control flow path with the following semantics:
        //     value0 <- ...
        //     [eventually move stack0 to stack1, perhaps via multiple copies]
        //     f(stack1)
        // In this execution, `value0` has not been saved to `stack0`, and so `stack0` must have
        // been produced by something older than this store to `value0` -- but since it's the first
        // store to `value0`, it must be produced from a different `valueN`. Therefore, `value0`
        // cannot be the only source of `stack1`, and so the concern is irrelevant.

        match source {
            Source::Value(value_var) => {
                arena[var.version] = Expression::Variable(value_var);
                // Drop the now-unused access to make sure that the replaced `stackN` use won't keep
                // `stackN` alive if it's otherwise unused. This is sufficient to guarantee no false
                // positives during the DFS stage in `splitting` because all remaining stack
                // accesses not for the purposes of stack manipulation are guaranteed to be part of
                // computations (which we consider to be side effects) and thus keep this `stackN`
                // use alive.
                //
                // Forgetting to do this this can cause subtle bugs, since the removed `stackN`
                // acting as a GC root can cause other linked-out stack definitions to become live,
                // preventing the algorithm for removing dead definitions in `main_opt` from
                // converging in a single step, and eventually stopping certain expressions from
                // getting inlined.
                false
            }
            Source::Missing => unreachable!(),
            Source::Indeterminate => true,
        }
    });
}
