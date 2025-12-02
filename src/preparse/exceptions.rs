use super::{CatchHandler, basic_blocks::ExceptionHandler};
use crate::utils::merge_overlapping_ranges;

pub fn coalesce_exception_handlers(
    exception_handlers: Vec<ExceptionHandler<'_>>,
) -> Vec<CatchHandler<'_>> {
    // We assume that all exception handlers with matching `target` and `class` properties
    // correspond to the same `catch` block. This is not *guaranteed* to be true, but it's true for
    // javac and it's as intuitive as it gets. If we're mistaken, the worst that can happen is we
    // get a slightly worse output.

    // We can't just collect handlers into a hash map here because the order of exception handlers
    // matters, so we only look for consecutive matches. javac always generates such entries
    // consecutively.
    exception_handlers
        .chunk_by(|a, b| (a.target, a.class) == (b.target, b.class))
        .map(|chunk| {
            let ExceptionHandler { target, class, .. } = chunk[0];

            let mut active_ranges: Vec<_> = chunk
                .iter()
                .map(|handler| handler.active_range.clone())
                .collect();
            active_ranges.sort_unstable_by_key(|range| range.start);
            merge_overlapping_ranges(&mut active_ranges);
            assert!(!active_ranges.is_empty(), "no active ranges for `catch`");

            CatchHandler {
                active_ranges,
                target,
                class,
            }
        })
        .collect()
}
