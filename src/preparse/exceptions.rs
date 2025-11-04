use super::{CatchHandler, basic_blocks::ExceptionHandler};
use crate::ast::Str;
use crate::utils::merge_overlapping_ranges;
use core::ops::Range;
use rustc_hash::FxHashMap;

pub fn coalesce_exception_handlers(
    exception_handlers: Vec<ExceptionHandler<'_>>,
) -> Vec<CatchHandler<'_>> {
    // We assume that all exception handlers with matching `target` and `class` properties
    // correspond to the same `catch` block. This is not *guaranteed* to be true, but it's true for
    // javac and it's as intuitive as it gets. If we're mistaken, the worst that can happen is we
    // get a slightly worse output.
    let mut by_target_class: FxHashMap<(usize, Option<Str<'_>>), Vec<Range<usize>>> =
        FxHashMap::default();
    for handler in exception_handlers {
        by_target_class
            .entry((handler.target, handler.class))
            .or_default()
            .push(handler.active_range);
    }

    by_target_class
        .into_iter()
        .map(|((target, class), mut active_ranges)| {
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
