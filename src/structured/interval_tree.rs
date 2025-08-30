use core::ops::Range;

pub struct IntervalTree {
    max: usize,
    nodes: Vec<Node>,
}

#[derive(Clone, Debug)]
struct Node {
    by_start: Vec<(usize, usize)>, // (start, id)
    by_end: Vec<(usize, usize)>,   // (end, id)
}

impl IntervalTree {
    pub fn new(max: usize, intervals: impl Iterator<Item = (Range<usize>, usize)>) -> Self {
        let mut nodes = vec![
            Node {
                by_start: Vec::new(),
                by_end: Vec::new()
            };
            max.next_power_of_two()
        ];

        for (range, id) in intervals {
            if range.len() <= 1 {
                continue;
            }

            assert!(range.end <= max, "range out of bounds");

            let mut v = 1;
            let mut node_range = 0..max;
            loop {
                let mid = node_range.start.midpoint(node_range.end);
                if range.end <= mid {
                    v *= 2;
                    node_range = node_range.start..mid;
                } else if range.start >= mid {
                    v = v * 2 + 1;
                    node_range = mid..node_range.end;
                } else {
                    nodes[v].by_start.push((range.start, id));
                    nodes[v].by_end.push((range.end, id));
                    break;
                }
            }
        }

        for node in &mut nodes {
            node.by_start
                .sort_unstable_by_key(|(start, _)| core::cmp::Reverse(*start));
            node.by_end.sort_unstable_by_key(|(end, _)| *end);
        }

        Self { max, nodes }
    }

    // Returns and removes the interval from the list. May yield an interval more than once, even
    // across invocations after being removed, but always at most O(1) times.
    pub fn extract_containing(&mut self, point: usize) -> impl Iterator<Item = usize> {
        let mut v = 1;
        let mut node_range = 0..self.max;

        core::iter::from_fn(move || {
            loop {
                let mid = node_range.start.midpoint(node_range.end);
                if point < mid {
                    if let Some((_, id)) =
                        self.nodes[v].by_start.pop_if(|(start, _)| *start < point)
                    {
                        return Some(id);
                    }
                    v *= 2;
                    node_range = node_range.start..mid;
                } else {
                    if let Some((_, id)) = self.nodes[v].by_end.pop_if(|(end, _)| point < *end) {
                        return Some(id);
                    }
                    if point == mid {
                        return None;
                    }
                    v = v * 2 + 1;
                    node_range = mid..node_range.end;
                }
            }
        })
    }
}
