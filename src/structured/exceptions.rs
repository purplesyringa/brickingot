use crate::linear::CatchHandler;
use alloc::collections::BTreeMap;
use core::ops::Range;

/// Compute and return consistent syntactic ranges for `catch` handlers encompassing all active
/// ranges, such that each range #i either contains or doesn't intersect range #j for all i > j.
/// Does not reorder handlers.
pub fn compute_syntactic_eh_ranges(handlers: &[CatchHandler<'_>]) -> Vec<Range<usize>> {
    let mut covered_ranges = BTreeMap::new(); // start -> end
    let mut syntactic_ranges = Vec::with_capacity(handlers.len());

    for handler in handlers {
        let mut syn_start;
        let mut syn_end;

        if handler.active_ranges.is_empty() {
            // If there are no active ranges associated with the handler, the only purpose of this
            // `try`..`catch` block is to demonstrate that a) there has once been some code within
            // `try`, b) what the handler is. Placing an empty `try {}` just before the handler
            // sounds like a good approach.
            syn_start = handler.body.jump_target;
            syn_end = handler.body.jump_target;
        } else {
            syn_start = handler.active_ranges[0].start;
            // If `end < jump_target`, we have to either emit a forward jump or extend the `try`
            // block to `jump_target`. The former doesn't handle finalizers correctly because it
            // effectively jumps over the finalizer, complicating everything. The latter solution
            // works and is also easier to implement.
            syn_end = handler
                .active_ranges
                .last()
                .unwrap()
                .end
                .max(handler.body.jump_target);
        }

        // Find the subset of ranges intersecting `syn_start..syn_end`. Unfortunately, this has to
        // be hacky without cursors.
        let it_start = covered_ranges
            .range(..syn_start)
            .last()
            .map(|(start, _)| *start)
            .unwrap_or(0);
        for (start, end) in
            covered_ranges.extract_if(it_start..syn_end, move |_, end| *end > syn_start)
        {
            // Make the new syntactic range encompass the existing ones.
            syn_start = syn_start.min(start);
            syn_end = syn_end.max(end);
        }

        covered_ranges.insert(syn_start, syn_end);

        syntactic_ranges.push(syn_start..syn_end);
    }

    syntactic_ranges
}
