use core::ops::Range;

#[derive(Default)]
pub struct IntervalTree {
    nodes: Vec<Node>,
}

#[derive(Clone, Debug)]
struct Node {
    by_start: Vec<(usize, usize)>, // (start, id)
    by_end: Vec<(usize, usize)>,   // (end, id)
}

impl IntervalTree {
    pub fn new(max: usize, ranges: impl Iterator<Item = (usize, Range<usize>)>) -> Self {
        let mut nodes = vec![
            Node {
                by_start: Vec::new(),
                by_end: Vec::new()
            };
            max
        ];

        for (id, range) in ranges {
            assert!(range.end <= max, "range out of bounds");
            if range.is_empty() {
                continue;
            }
            let mid = (range.end & (usize::MAX << (range.start ^ range.end).ilog2())) - 1;
            nodes[mid].by_start.push((range.start, id));
            nodes[mid].by_end.push((range.end, id));
        }

        for node in &mut nodes {
            node.by_start
                .sort_unstable_by_key(|(start, _)| core::cmp::Reverse(*start));
            node.by_end.sort_unstable_by_key(|(end, _)| *end);
        }

        Self { nodes }
    }

    // Returns and removes the range from the list. May yield a range more than once, even across
    // invocations after being removed, but always at most O(1) times.
    pub fn drain_containing(&mut self, point: usize) -> impl Iterator<Item = usize> {
        assert!(point < self.nodes.len(), "out of bounds");

        let mut mid = point;
        let end = (2 << self.nodes.len().ilog2()) - 1;

        core::iter::from_fn(move || {
            while mid < end {
                if let Some(node) = self.nodes.get_mut(mid) {
                    let popped = if point < mid {
                        node.by_start.pop_if(|(start, _)| *start <= point)
                    } else {
                        node.by_end.pop_if(|(end, _)| point < *end)
                    };
                    if let Some((_, id)) = popped {
                        return Some(id);
                    }
                }
                mid = (mid | (mid + 1)) & !(2 << mid.trailing_ones());
            }
            None
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::collection::vec;
    use proptest::prelude::*;

    prop_compose! {
        fn range(max: usize)(a in 0..max, b in 0..max) -> Range<usize> {
            a.min(b)..a.max(b) + 1
        }
    }

    prop_compose! {
        fn data()(max in 1usize..32)(max in Just(max), ranges in vec(range(max), 10), point in 0..max) -> (usize, Vec<Range<usize>>, usize) {
            (max, ranges, point)
        }
    }

    proptest! {
        #[test]
        fn works_once((max, ranges, point) in data()) {
            let mut itree_output: Vec<usize> =
                IntervalTree::new(max, ranges.iter().cloned().enumerate())
                    .drain_containing(point)
                    .collect();
            itree_output.sort();

            let expected_output: Vec<usize> = ranges
                .into_iter()
                .enumerate()
                .filter(|(_, range)| range.contains(&point))
                .map(|(id, _)| id)
                .collect();

            prop_assert_eq!(itree_output, expected_output);
        }
    }
}
