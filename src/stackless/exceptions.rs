// `try` blocks are not guaranteed to be nested correctly. Even if nested, the outer `try` block can
// have more priority than the inner one.
//
// There's no better way to handle this than forcing the inner `try` block to be as large as the
// outer one. But that would require not just its left end, but also its right end to be extended,
// which would change the position of `catch` and force us to insert a backward jump. We thus need
// to perform these extensions before the requirement list is generated. That's what
// `treeify_try_blocks` does.
//
// We need to make sure that syntactic extension of the `try` range does not affect semantics, which
// we do by creating a synthetic variable that effectively tracks the program counter. We could do
// it slightly differently by creating a per-`try`-block synthetic `bool` variable that tracks EH
// eligibility, but that would be superlinear in the worst case. Since incorrectly nested `try`
// blocks should only occur in obfuscated code, it's likely that this worst case would in fact be
// reached in practice, so a single variable will hopefully be simpler not just for us, but for the
// end user as well.

use super::{ExceptionHandler, Program, Statement};
use crate::ast::{
    Arena, BasicStatement, BinOp, Expression, LogicalOp, Variable, VariableName, VariableNamespace,
};
use alloc::collections::BTreeMap;
use core::cmp::Reverse;
use core::ops::Range;

#[derive(Clone)]
struct ExtendedHandler {
    handler_id: usize,
    active_range: Range<usize>,
}

pub fn legalize_exception_handling<'code>(arena: &mut Arena<'code>, program: &mut Program<'code>) {
    let extended_handlers = treeify_try_blocks(&mut program.exception_handlers);
    if extended_handlers.is_empty() {
        return;
    }

    let (context_ids, handler_context_ids) = compute_contexts(
        program.basic_blocks.len(),
        &extended_handlers
            .iter()
            .map(|handler| handler.active_range.clone())
            .collect::<Vec<_>>(),
    );

    // This allocates a single version for the context variables, which is not exactly optimal, but
    // more than fine for readability.
    let context_version = arena.alloc(Expression::Null);
    let context_var = || {
        arena.alloc(Expression::Variable(Variable {
            name: VariableName {
                id: 0,
                namespace: VariableNamespace::Context,
            },
            version: context_version,
        }))
    };

    // Add context checks to exception handlers.
    for (handler, context_id_range) in extended_handlers.into_iter().zip(handler_context_ids) {
        let condition = if context_id_range.len() == 1 {
            arena.alloc(Expression::BinOp {
                op: BinOp::Eq,
                lhs: context_var(),
                rhs: arena.int(context_id_range.start as i32),
            })
        } else {
            arena.alloc(Expression::LogicalOp {
                op: LogicalOp::And,
                lhs: arena.alloc(Expression::BinOp {
                    op: BinOp::Ge,
                    lhs: context_var(),
                    rhs: arena.int(context_id_range.start as i32),
                }),
                rhs: arena.alloc(Expression::BinOp {
                    op: BinOp::Le,
                    lhs: context_var(),
                    rhs: arena.int(context_id_range.end as i32 - 1),
                }),
            })
        };

        program.exception_handlers[handler.handler_id]
            .body
            .condition = Some(condition);
    }

    // Assign contexts.
    //
    // The invariant here is that, on entry to each basic block, the correct context ID is stored in
    // the synthetic. This allows us to remove assignments in basic blocks whose predecessors all
    // have the same context ID. This does not result in the *minimal* number of assignments, but
    // that's not our goal -- we mostly want code to stay readable, and this seems more intuitive
    // than solving a problem that is likely NP-hard.
    for (bb_id, (bb, context_id)) in program
        .basic_blocks
        .iter_mut()
        .zip(&context_ids)
        .enumerate()
    {
        // Always assign at the entry to the function. This kind of acts as the base case of
        // recursion.
        if bb_id != 0
            && bb
                .predecessors
                .iter()
                .all(|pred_bb_id| context_ids[*pred_bb_id] == *context_id)
        {
            continue;
        }

        bb.statements.insert(
            0,
            Statement::Basic(BasicStatement::Assign {
                target: context_var(),
                value: arena.int(*context_id as i32),
            }),
        )
    }
}

// Extends exception handler ranges such that each range #i either contains or doesn't intersect
// range #j for all i > j. Does not reorder handlers. Returns information about the extended
// handlers.
fn treeify_try_blocks(handlers: &mut [ExceptionHandler<'_>]) -> Vec<ExtendedHandler> {
    let mut active_ranges = BTreeMap::new(); // start -> end
    let mut extended_handlers = Vec::new();

    for (handler_id, handler) in handlers.iter_mut().enumerate() {
        // Typically, the `try` block range ends before the handler; in this case, we emit
        // a slightly larger `try` block so that the handler directly follows its end and `catch`
        // can fallthrough into the handler without any explicit jumps. If the range contains more
        // statements than necessary, we'll sort it out later with synthetic variables.
        //
        // We could also emit `start..end` and a forward jump, but it's not yet clear if that's any
        // better, since that might be harder to optimize.
        let mut new_start = handler.active_range.start;
        let mut new_end = handler.active_range.end.max(handler.body.jump_target);

        // Find the subset of ranges intersecting `new_start..new_end`. Unfortunately, this has to
        // be hacky without cursors.
        let it_start = active_ranges
            .range(..new_start)
            .last()
            .map(|(start, _)| *start)
            .unwrap_or(0);
        for (start, end) in
            active_ranges.extract_if(it_start..new_end, move |_, end| *end > new_start)
        {
            // Make the new range encompass the old ones.
            new_start = new_start.min(start);
            new_end = new_end.max(end);
        }

        active_ranges.insert(new_start, new_end);

        let new_range = new_start..new_end;
        if handler.active_range != new_range {
            extended_handlers.push(ExtendedHandler {
                handler_id,
                active_range: handler.active_range.clone(),
            });
            handler.active_range = new_range;
        }
    }

    extended_handlers
}

// For each point in `0..n_points`, compute a context ID that uniquely represents the set of ranges
// containing that point. Additionally, for each range, compute the interval of context IDs on that
// range.
fn compute_contexts(n_points: usize, ranges: &[Range<usize>]) -> (Vec<usize>, Vec<Range<usize>>) {
    // If I had more time, I would have written a shorter letter, or something like that. Not sure
    // how to simplify this further without hashing.

    // Iterate over events in the natural order.
    struct Event {
        is_open: bool,
        range_id: usize,
    }
    let mut events: Vec<Event> = (0..ranges.len())
        .flat_map(|range_id| [false, true].map(|is_open| Event { is_open, range_id }))
        .collect();
    events.sort_by_key(|event| {
        let range = &ranges[event.range_id];
        if event.is_open {
            (range.start, true, Reverse(range.end))
        } else {
            (range.end, false, Reverse(range.start))
        }
    });
    let mut events = events.into_iter().peekable();

    // The indices of currently open ranges, ordered by their start.
    let mut range_stack: Vec<usize> = Vec::new();
    // The position of the given range in stack, or `usize::MAX` if absent.
    let mut pos_in_stack: Vec<usize> = vec![usize::MAX; ranges.len()];

    // Saved indices of prefixes: `(len, id)` means that the set `range_stack[..len]` is
    // associated with context ID `id`. Lack of `len` in the stack means that the set has not been
    // assigned any ID yet.
    let mut id_stack: Vec<(usize, usize)> = Vec::new();
    let mut next_id = 0;

    let mut point_context_ids = Vec::with_capacity(n_points);
    let mut range_context_ranges = vec![0..0; ranges.len()];

    for point in 0..n_points {
        while let Some(event) = events.next_if(|event| {
            let range = &ranges[event.range_id];
            (if event.is_open {
                range.start
            } else {
                range.end
            }) == point
        }) {
            if event.is_open {
                // A new range has just opened. This context is guaranteed to be distinct from all
                // contexts thus far. We'll create a new one in a bit.
                pos_in_stack[event.range_id] = range_stack.len();
                range_stack.push(event.range_id);
                // Since all context IDs within this range are distinct from everything we've seen
                // so far, the minimum boundary is `next_id`.
                range_context_ranges[event.range_id].start = next_id;
            } else {
                // A range has just closed -- drop it from the stack.
                let pos = pos_in_stack[event.range_id];
                pos_in_stack[*range_stack.last().expect("range stack is empty")] = pos;
                pos_in_stack[event.range_id] = usize::MAX;
                range_stack.swap_remove(pos);
                // Removing a range from the middle of the list invalidates context IDs of all
                // prefixes that contain that range.
                // |-------------|
                //    |---------------------|
                //         |-----------|
                //               ^ we're here
                //                ^^^^^^^^^^ none of these sets can possibly match any set from
                //                           before, so we'll only ever encounter old IDs if we pop
                //                           the whole suffix since `pos`.
                // It doesn't matter that we modify the order of the following ranges in the stack
                // because the order of ranges that have opened in a now-closed range is
                // indistinguishable.
                while id_stack.pop_if(|(len, _)| pos < *len).is_some() {}
                // Every context ID in this range has been below `next_id`, and everything after
                // this range is guaranteed not to match any of the context IDs we've created while
                // the range was active.
                range_context_ranges[event.range_id].end = next_id;
            }
        }

        if id_stack
            .last()
            .is_none_or(|(len, _)| *len != range_stack.len())
        {
            id_stack.push((range_stack.len(), next_id));
            next_id += 1;
        }
        point_context_ids.push(id_stack.last().unwrap().1);
    }

    (point_context_ids, range_context_ranges)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rustc_hash::FxHashMap;

    prop_compose! {
        fn range(max: usize)(a in 0..max, b in 0..max) -> Range<usize> {
            a.min(b)..a.max(b) + 1
        }
    }

    proptest! {
        #[test]
        fn correct_context_ids(n_points in Just(11), ranges in vec(range(10), 5)) {
            let alg_contexts = compute_contexts(n_points, &ranges).0;

            let mut sets = vec![Vec::new(); n_points];
            for (range_id, range) in ranges.iter().enumerate() {
                for i in range.clone() {
                    sets[i].push(range_id);
                }
            }
            let mut cached_ids = FxHashMap::default();
            let expected_contexts: Vec<usize> = sets.into_iter().map(|set| {
                let next_context_id = cached_ids.len();
                *cached_ids.entry(set).or_insert(next_context_id)
            }).collect();

            prop_assert_eq!(alg_contexts, expected_contexts);
        }
    }

    proptest! {
        #[test]
        fn range_maps_to_interval_of_ranges(n_points in Just(11), ranges in vec(range(10), 5)) {
            let (context_ids, range_context_ranges) = compute_contexts(n_points, &ranges);

            for (range, range_context_ids) in ranges.iter().cloned().zip(range_context_ranges) {
                for (point, context_id) in context_ids.iter().enumerate() {
                    let is_in_point_range = range.contains(&point);
                    let is_in_context_range = range_context_ids.contains(&context_id);
                    prop_assert_eq!(is_in_point_range, is_in_context_range);
                }
            }
        }
    }
}
