use rustc_hash::FxHashMap;

use super::gap_tracker::GapTracker;
use super::interval_tree::IntervalTree;
use crate::stackless;
use alloc::collections::BTreeMap;
use core::ops::Range;

#[derive(Debug)]
pub enum Node {
    Linear {
        stmt_range: Range<usize>,
    },
    Block {
        id: usize,
        children: Vec<Node>,
    },
    Try {
        id: usize,
        children: Vec<Node>,
    },
    DispatchSwitch {
        dispatch_targets: Vec<DispatchTarget>,
    },
}

#[derive(Debug)]
pub struct DispatchTarget {
    pub selector: i32,
    pub jump_req_id: usize,
}

/// Represents that there must exist a block covering at least the given statement region and
/// capable of implementing the given behavior.
#[derive(Clone, Debug)]
pub struct BlockRequirement {
    pub range: Range<usize>,
    pub kind: RequirementKind,
}

#[derive(Clone, Debug)]
pub enum RequirementKind {
    /// The block must allow jumps to `range.start` via `break`.
    BackwardJump,
    /// The block must allow jumps to `range.end` via `continue`.
    ForwardJump,
    /// The block must catch exceptions.
    Try {
        /// ...and optionally jump according to this requirement in `catch`.
        with_backward_jump: Option<usize>,
    },
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum RequirementKey {
    /// A forward or backward jump to some target.
    Jump { stmt_index: usize },
    /// `case` or `default` in a `switch`.
    Switch { stmt_index: usize, key: Option<i32> },
    /// A `try` block.
    Try { index: usize },
    /// A backward jump from `catch` to the real exception handler.
    BackwardCatch { index: usize },
    /// A synthetic jump.
    Dispatch { id: usize },
}

#[derive(Clone)]
pub enum RequirementImplementation {
    Break { block_id: usize },
    Continue { block_id: usize },
    ContinueToDispatcher { block_id: usize, selector: i32 },
    Try { block_id: usize },
}

pub fn compute_block_requirements(
    stackless_ir: &stackless::Program<'_>,
) -> (Vec<BlockRequirement>, Vec<RequirementKey>) {
    let jump = |from: usize, to: usize| {
        if from < to {
            // There must be a block covering instruction `from` and ending at `to`.
            BlockRequirement {
                range: from..to,
                kind: RequirementKind::ForwardJump,
            }
        } else {
            // There must be a block covering instruction `from` and beginning at `to`.
            BlockRequirement {
                range: to..from + 1,
                kind: RequirementKind::BackwardJump,
            }
        }
    };

    let mut requirements = Vec::new();
    let mut keys = Vec::new();

    // Jumps are satisfied by normal blocks.
    for (stmt_index, stmt) in stackless_ir.statements.iter().enumerate() {
        match stmt {
            stackless::Statement::Basic(_) | stackless::Statement::Label { .. } => {}
            stackless::Statement::Jump { target, .. } => {
                keys.push(RequirementKey::Jump { stmt_index });
                requirements.push(jump(stmt_index, *target));
            }
            stackless::Statement::Switch { arms, default, .. } => {
                for (key, successor) in arms {
                    keys.push(RequirementKey::Switch {
                        stmt_index,
                        key: Some(*key),
                    });
                    requirements.push(jump(stmt_index, *successor));
                }
                keys.push(RequirementKey::Switch {
                    stmt_index,
                    key: None,
                });
                requirements.push(jump(stmt_index, *default));
            }
        }
    }

    // `try` blocks are not guaranteed to be nested correctly. Even if nested, the outer `try` block
    // can have more priority than the inner one. There's no better way to handle this than forcing
    // the inner `try` block to be as large as the outer one. But that would require not just its
    // left end, but also its right end to be extended, which would change the position of `catch`
    // and force us to insert a backward jump. We thus need to perform these extensions before the
    // requirement list is generated. `treeify_try_blocks` is responsible for doing this.
    for (index, handler) in treeify_try_blocks(&stackless_ir.exception_handlers)
        .into_iter()
        .enumerate()
    {
        let with_backward_jump = if handler.end == handler.target {
            // If `handler.target > handler.end`, `treeify_try_blocks` would have extended `end`.
            None
        } else {
            // If the handler is located before or within the `try` block, we have to emit a jump.
            //
            // The problem is that since the `try` block and the jump have matching ends, it's
            // possible that the jump ends up nested within `try`; but `catch` does not have access
            // to `try` internals since it's located *after* `try`, not at the end of `try`. We want
            // to force the jump to be handled before `try` regardless of apparent nesting.
            //
            // A special variation of this problem arises if the handler is inside `try`: if we
            // split `try` into two parts and handled them separately, and a smaller nested `try`
            // block crosses `handler.target`, we would have an invalid tree; moreover, since each
            // individual part can be smaller than the nested `try` block, the `try` order may
            // become swapped. This forces us to emit a single `try` even if it produces worse
            // codegen.
            let jump_req_id = requirements.len();
            keys.push(RequirementKey::BackwardCatch { index });
            requirements.push(BlockRequirement {
                range: handler.target..handler.end,
                kind: RequirementKind::BackwardJump,
            });
            Some(jump_req_id)
        };

        keys.push(RequirementKey::Try { index });
        requirements.push(BlockRequirement {
            range: handler.start..handler.end,
            kind: RequirementKind::Try { with_backward_jump },
        });
    }

    (requirements, keys)
}

// Extends exception handler ranges such that each range #i either contains or doesn't intersect
// range #j for all i > j. Does not reorder handlers.
fn treeify_try_blocks<'code>(
    handlers: &[stackless::ExceptionHandler<'code>],
) -> Vec<stackless::ExceptionHandler<'code>> {
    let mut active_ranges = BTreeMap::new(); // start -> end

    let mut handlers = Vec::from(handlers);
    for handler in &mut handlers {
        // Typically, the `try` block range ends before the handler; in this case, we emit
        // a slightly larger `try` block so that the handler directly follows its end and `catch`
        // can fallthrough into the handler without any explicit jumps. If the range contains more
        // statements than necessary, we'll sort it out later with synthetic variables.
        //
        // We could also emit `handler.start..handler.end` and a forward jump, but it's not yet
        // clear if that's any better, since that might be harder to optimize.
        let mut new_start = handler.start;
        let mut new_end = handler.end.max(handler.target);

        // Find the subset of ranges intersecting `new_start..new_end`. Unfortunately, this has to
        // be hacky without cursors.
        let it_start = active_ranges
            .range(..new_start)
            .last()
            .map(|(start, _)| *start)
            .unwrap_or(0);
        for (start, end) in active_ranges.extract_if(it_start..new_end, move |start, end| {
            *start < new_end && *end > new_start
        }) {
            // Make the new range encompass the old ones.
            new_start = new_start.min(start);
            new_end = new_end.max(end);
        }

        active_ranges.insert(new_start, new_end);
        handler.start = new_start;
        handler.end = new_end;
    }

    handlers
}

pub fn satisfy_block_requirements(
    program_len: usize,
    mut block_requirements: Vec<BlockRequirement>,
) -> (Vec<Node>, Vec<RequirementImplementation>, usize) {
    if block_requirements.is_empty() {
        // Helps to reduce the constant factor a bit in the common case.
        return (
            vec![Node::Linear {
                stmt_range: 0..program_len,
            }],
            Vec::new(),
            1,
        );
    }

    // The general approach we follow to translate possibly contradictory requirements to a tree
    // structures is described here:
    // https://purplesyringa.moe/blog/recovering-control-flow-structures-without-cfgs/.
    //
    // In a nutshell, at each step, we select a segment entirely covered by ranges of requirements
    // and place a block at that segment; we then remove requirements that are satisfied by this
    // block. For example, if there are requirements "1..4 backward" and "2..7 forward", we will
    // create a block covering 1..7 and satisfy both.
    //
    // This leaves out combinations like "1..3 forward, 2..5 backward", which cannot be implemented
    // with non-overlapping blocks:
    //     ----->       the head of this arrow cannot be extended
    //        <------   and neither can the head of this one
    // In cases like this, we can implement the backward jump in two stages via a dispatcher:
    //     {        }   outer block
    //     { }          inner block
    //     ----->       this jump stays as-is
    //     <---------   this one jumps to the beginning of the outer block
    //     -->          this one jumps via `break` in of the inner block
    // In effect, we rewrite certain requirements on the fly.
    //
    // While jumps are independent, `try` blocks and jumps from `catch`es aren't, meaning that we
    // want to retain nesting order in some cases. For example,
    //     block #1 {
    //         try #2 {
    //             f();
    //         } catch {
    //             continue #1;
    //         }
    //     }
    // is valid, while
    //     try #1 {
    //         block #2 {
    //             f();
    //         }
    //     } catch {
    //         continue #2;
    //     }
    // isn't, even though the ranges of `block` and `try` requirements are the same. In addition,
    // the order in which `catch` closures match types matters since one catch a subclass of the
    // other.

    // Many data structures here are indiced by statement ID -- don't waste cache on whitespace.
    let mut used_indices: Vec<usize> = [0, program_len]
        .into_iter()
        .chain(
            block_requirements
                .iter()
                .flat_map(|req| [req.range.start, req.range.end]),
        )
        .collect();
    used_indices.sort();
    used_indices.dedup();
    for req in &mut block_requirements {
        req.range.start = used_indices.binary_search(&req.range.start).unwrap();
        req.range.end = used_indices.binary_search(&req.range.end).unwrap();
    }
    let n_statements = used_indices.len() - 1;

    let mut req_cover = GapTracker::new(n_statements);
    let mut backward_jumps_to = vec![Vec::new(); n_statements];
    let mut backward_jumps = Vec::new();

    // The ends of `try` blocks cannot be extended, since they serve as `catch` targets. They are
    // similar to forward jumps in this regard, which is why they are grouped together.
    let mut forward_or_try_req_cover = GapTracker::new(n_statements);
    let mut forward_jumps_to = vec![Vec::new(); n_statements + 1];
    let mut tries_to = vec![Vec::new(); n_statements + 1];

    for (i, req) in block_requirements.iter().enumerate() {
        req_cover.add_segment(req.range.clone());
        match req.kind {
            RequirementKind::BackwardJump => {
                backward_jumps_to[req.range.start].push(i);
                backward_jumps.push((req.range.clone(), i));
            }
            RequirementKind::ForwardJump => {
                forward_jumps_to[req.range.end].push(i);
                forward_or_try_req_cover.add_segment(req.range.clone());
            }
            RequirementKind::Try { .. } => {
                // Largest `try` block goes last.
                tries_to[req.range.end].push(i);
                forward_or_try_req_cover.add_segment(req.range.clone());
            }
        }
    }
    let backward_jumps = IntervalTree::new(n_statements, backward_jumps.into_iter());
    let imps = vec![None; block_requirements.len()];

    let mut treeificator = Treeificator {
        reqs: block_requirements,
        req_cover,
        backward_jumps_to,
        backward_jumps,
        forward_or_try_req_cover,
        forward_jumps_to,
        tries_to,
        imps,
        next_block_id: 1,
        dispatcher_at_stmt: FxHashMap::default(),
        used_indices,
    };

    let tree = treeificator.build_list(0..n_statements);

    (
        tree,
        treeificator
            .imps
            .into_iter()
            .map(|imp| imp.expect("unimplemented block requirement"))
            .collect(),
        treeificator.next_block_id,
    )
}

struct Treeificator {
    reqs: Vec<BlockRequirement>,
    req_cover: GapTracker,
    backward_jumps: IntervalTree,
    backward_jumps_to: Vec<Vec<usize>>,
    forward_or_try_req_cover: GapTracker,
    forward_jumps_to: Vec<Vec<usize>>,
    tries_to: Vec<Vec<usize>>,
    imps: Vec<Option<RequirementImplementation>>,
    next_block_id: usize,
    dispatcher_at_stmt: FxHashMap<usize, Dispatcher>,
    used_indices: Vec<usize>,
}

#[derive(Debug, Default)]
struct Dispatcher {
    known_targets: FxHashMap<usize, DispatchTarget>,
}

impl Treeificator {
    fn build_list(&mut self, range: Range<usize>) -> Vec<Node> {
        let mut prev_gap = range.start;
        let mut nodes = Vec::new();
        while let Some(gap) = self.req_cover.first_gap(prev_gap..range.end) {
            self.build_single_block(prev_gap..gap, &mut nodes);
            prev_gap = gap;
        }
        self.build_single_block(prev_gap..range.end, &mut nodes);
        nodes
    }

    fn build_single_block(&mut self, range: Range<usize>, out: &mut Vec<Node>) {
        // The goal here is to handle enough requirements such that a new gap appears within the
        // range.

        // By the time this function is entered, no jumps cover the range strictly.

        // Create a block, ostensibly for jumps.
        let block_id = self.next_block_id;
        self.next_block_id += 1;
        let mut found_jumps = false;

        // Handle simple jumps.
        for req_id in self.backward_jumps_to[range.start].drain(..) {
            if self.imps[req_id].is_some() {
                // Already discharged during head-to-head collision resolving.
                continue;
            }
            self.req_cover
                .remove_segment(self.reqs[req_id].range.clone());
            self.imps[req_id] = Some(RequirementImplementation::Break { block_id });
            found_jumps = true;
        }
        for req_id in self.forward_jumps_to[range.end].drain(..) {
            let range = self.reqs[req_id].range.clone();
            self.req_cover.remove_segment(range.clone());
            self.forward_or_try_req_cover.remove_segment(range);
            self.imps[req_id] = Some(RequirementImplementation::Continue { block_id });
            found_jumps = true;
        }

        // Recognize backward jumps forming head-to-head collisions that need to be resolved via
        // this block.
        if let Some(forward_gap) = self.forward_or_try_req_cover.first_gap(range.clone()) {
            let mut backward_jumps = core::mem::take(&mut self.backward_jumps);
            for req_id in backward_jumps.extract_containing(forward_gap) {
                if self.imps[req_id].is_some() {
                    // Either extracted twice or already removed.
                    continue;
                }
                // Implement this jump with a jump to the dispatcher.
                self.req_cover
                    .remove_segment(self.reqs[req_id].range.clone());
                self.imps[req_id] =
                    Some(self.add_dispatch(block_id, range.start, self.reqs[req_id].range.start));
                found_jumps = true;
            }
            self.backward_jumps = backward_jumps;
        }

        if found_jumps {
            out.push(Node::Block {
                id: block_id,
                children: self.build_list(range),
            });
            return;
        }

        // Look for `try` blocks only after greedily matching jumps. This guarantees that `try`
        // blocks are always nested within normal blocks if their nesting order is indeterminate,
        // which is necessary for correct backward jump handling.
        //
        // It also guarantees that `try` blocks are only as small as necessary. Had we swapped this
        // around, `try` with `continue` within a loop would get extended to span the whole loop,
        // creating a mess.
        //
        // There are a few slight issues here, though. Specifically, loops at the beginning of `try`
        // will be decoded as
        //     block #1 {
        //         try #2 {
        //             ...
        //             continue #1;
        //             ...
        //         } catch { ... }
        //     }
        // instead of
        //    try #1 {
        //         block #2 {
        //             ...
        //             continue #2;
        //             ...
        //         }
        //         ...
        //     } catch { ... }
        // It's not that big of a deal, since we have to deal with this for nested loops anyway, but
        // it's good to keep in mind.
        //
        // We only take out the largest `try` block here, since smaller ones ending at the same
        // location cannot really be easily implemented with the same `try`, unlike with forward
        // jumps. The `try` block is thus only extended as much as necessary if it has multiple
        // entries.

        if let Some(req_id) = self.tries_to[range.end].last()
            && let RequirementKind::Try {
                with_backward_jump: Some(jump_req_id),
            } = self.reqs[*req_id].kind
            && self.imps[jump_req_id].is_none()
        {
            // If there backward jump from `catch` hasn't been implemented yet, emit a block for it
            // right now, since this is the last chance to generate it outside `try`.
            let BlockRequirement {
                range: jump_range,
                kind: RequirementKind::BackwardJump,
            } = self.reqs[jump_req_id].clone()
            else {
                panic!("unexpected requirement pair for try");
            };
            assert_eq!(
                jump_range.end, range.end,
                "invalid backward jump from catch"
            );
            let target = jump_range.start;

            self.req_cover.remove_segment(jump_range.clone());

            let imp = if target == range.start {
                // Jump directly to the beginning of the block, can be a normal backward jump.
                RequirementImplementation::Break { block_id }
            } else {
                // Jump via dispatcher.
                self.add_dispatch(block_id, range.start, target)
            };
            self.imps[jump_req_id] = Some(imp);

            out.push(Node::Block {
                id: block_id,
                children: self.build_list(range),
            });
            return;
        }

        if let Some(req_id) = self.tries_to[range.end].pop() {
            let try_range = self.reqs[req_id].range.clone();
            self.req_cover.remove_segment(try_range.clone());
            self.forward_or_try_req_cover
                .remove_segment(try_range.clone());
            self.imps[req_id] = Some(RequirementImplementation::Try { block_id });
            out.push(Node::Try {
                id: block_id,
                children: self.build_list(range),
            });
            return;
        }

        // If there is nothing preventing a gap from appearing but there still isn't a gap, it must
        // be a range of length 1.
        assert_eq!(range.len(), 1, "failed to manifest a gap");

        if let Some(dispatcher) = self.dispatcher_at_stmt.remove(&range.start)
            && !dispatcher.known_targets.is_empty()
        {
            let mut dispatch_targets: Vec<DispatchTarget> =
                dispatcher.known_targets.into_values().collect();
            dispatch_targets.sort_unstable_by_key(|target| target.selector);
            out.push(Node::DispatchSwitch { dispatch_targets });
        }

        out.push(Node::Linear {
            // Decompress coordinates
            stmt_range: self.used_indices[range.start]..self.used_indices[range.end],
        });
    }

    fn add_dispatch(
        &mut self,
        block_id: usize,
        dispatcher: usize,
        target: usize,
    ) -> RequirementImplementation {
        let dispatcher_obj = self.dispatcher_at_stmt.entry(dispatcher).or_default();

        let next_selector = (dispatcher_obj.known_targets.len() + 1)
            .try_into()
            .expect("too many jumps");
        let target = dispatcher_obj
            .known_targets
            .entry(target)
            .or_insert_with(|| {
                // Create a new dispatch forward jump.
                let jump_req = BlockRequirement {
                    range: dispatcher..target,
                    kind: RequirementKind::ForwardJump,
                };
                let jump_req_id = self.reqs.len();
                self.req_cover.add_segment(jump_req.range.clone());
                self.forward_jumps_to[jump_req.range.end].push(jump_req_id);
                self.forward_or_try_req_cover
                    .add_segment(jump_req.range.clone());
                self.reqs.push(jump_req);
                self.imps.push(None);

                DispatchTarget {
                    selector: next_selector,
                    jump_req_id,
                }
            });

        RequirementImplementation::ContinueToDispatcher {
            block_id,
            selector: target.selector,
        }
    }
}
