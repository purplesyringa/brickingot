use core::ops::Range;

// Assumes the ranges are sorted by `start`. Removes empty ranges.
pub fn merge_overlapping_ranges(ranges: &mut Vec<Range<usize>>) {
    let mut out_len = 0;
    for input_i in 0..ranges.len() {
        let range = &ranges[input_i];
        if range.is_empty() {
            continue;
        }
        if out_len > 0 && range.start <= ranges[out_len - 1].end {
            ranges[out_len - 1].end = ranges[out_len - 1].end.max(range.end);
        } else {
            ranges[out_len] = range.clone();
            out_len += 1;
        }
    }
    ranges.truncate(out_len);
}
