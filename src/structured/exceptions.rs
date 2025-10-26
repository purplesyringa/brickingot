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

use crate::stackless;
use alloc::collections::BTreeMap;
use core::cmp::Reverse;
use core::ops::Range;

#[derive(Clone)]
struct ExtendedHandler {
    handler_id: usize,
    bb_range: Range<usize>,
}

pub fn legalize_exception_handling(stackless_ir: &mut stackless::Program<'_>) {
    let extended_handlers = treeify_try_blocks(&mut stackless_ir.exception_handlers);
    if extended_handlers.is_empty() {
        return;
    }

    let context_ids = compute_contexts(
        stackless_ir.basic_blocks.len(),
        &extended_handlers
            .iter()
            .map(|handler| handler.bb_range.clone())
            .collect::<Vec<_>>(),
    );

    // TODO: insert synthetic assignments
}

// Extends exception handler ranges such that each range #i either contains or doesn't intersect
// range #j for all i > j. Does not reorder handlers. Returns information about the extended
// handlers.
fn treeify_try_blocks(handlers: &mut [stackless::ExceptionHandler<'_>]) -> Vec<ExtendedHandler> {
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
        let mut new_start = handler.stmt_range.start;
        let mut new_end = handler.stmt_range.end.max(handler.target_stmt);

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
        if handler.stmt_range != new_range {
            extended_handlers.push(ExtendedHandler {
                handler_id,
                bb_range: handler.bb_range.clone(),
            });
            handler.stmt_range = new_range;
        }
    }

    extended_handlers
}

// For each point in `0..n_points`, compute a context ID that uniquely represents the set of ranges
// containing that point.
fn compute_contexts(n_points: usize, ranges: &[Range<usize>]) -> Vec<u32> {
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
    let mut id_stack: Vec<(usize, u32)> = Vec::new();
    let mut next_id = 0;

    let mut result = Vec::with_capacity(n_points);
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
            }
        }

        if id_stack
            .last()
            .is_none_or(|(len, _)| *len != range_stack.len())
        {
            id_stack.push((range_stack.len(), next_id));
            next_id += 1;
        }
        result.push(id_stack.last().unwrap().1);
    }
    result
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
            let alg_contexts = compute_contexts(n_points, &ranges);

            let mut sets = vec![Vec::new(); n_points];
            for (range_id, range) in ranges.iter().enumerate() {
                for i in range.clone() {
                    sets[i].push(range_id);
                }
            }
            let mut cached_ids = FxHashMap::default();
            let expected_contexts: Vec<u32> = sets.into_iter().map(|set| {
                let next_context_id = cached_ids.len() as u32;
                *cached_ids.entry(set).or_insert(next_context_id)
            }).collect();

            prop_assert_eq!(alg_contexts, expected_contexts);
        }
    }
}
