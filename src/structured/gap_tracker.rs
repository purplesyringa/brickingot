// Implementation mostly follows the "Increment modifications, queries for maximum" section from
// https://codeforces.com/blog/entry/18051.
use core::ops::Range;

// A segment tree-based implementation.
pub struct GapTracker {
    // 1-indexed tree nodes.
    nodes: Vec<Node>,
}

#[derive(Clone, Debug)]
struct Node {
    // Implicitly added to each leaf within the subtree of `v`.
    increment: isize,
    // The minimal value within the subtree, increment from this node applied, increments from
    // parents not applied.
    minimum: isize,
}

impl GapTracker {
    pub fn new(n_statements: usize) -> Self {
        Self {
            nodes: vec![
                Node {
                    increment: 0,
                    minimum: 0,
                };
                n_statements.next_power_of_two() * 2
            ],
        }
    }

    fn range_increment(&mut self, range: Range<usize>, value: isize) {
        if range.is_empty() {
            return;
        }

        let leaves = self.nodes.len() / 2;

        let mut left = leaves + range.start;
        let mut right = leaves + range.end;
        while left < right {
            if left % 2 == 1 {
                self.nodes[left].increment += value;
                self.nodes[left].minimum += value;
                left += 1;
            }
            if right % 2 == 1 {
                right -= 1;
                self.nodes[right].increment += value;
                self.nodes[right].minimum += value;
            }
            left /= 2;
            right /= 2;
        }

        for mut v in [leaves + range.start, leaves + range.end - 1] {
            while v != 1 {
                v /= 2;
                self.nodes[v].minimum = self.nodes[v].increment
                    + self.nodes[v * 2].minimum.min(self.nodes[v * 2 + 1].minimum);
            }
        }
    }

    fn first_zero(&self, range: Range<usize>) -> Option<usize> {
        if range.is_empty() {
            return None;
        }

        let leaves = self.nodes.len() / 2;
        let mut v = leaves + range.start;

        let mut increments = 0; // accumulates increments from parents of v
        let mut tmp = v;
        while tmp != 1 {
            tmp /= 2;
            increments += self.nodes[tmp].increment;
        }

        // Find the first node containing a zero
        while increments + self.nodes[v].minimum != 0 {
            while v % 2 == 1 {
                v /= 2;
                increments -= self.nodes[v].increment;
            }
            if v == 0 {
                return None;
            }
            v += 1;
        }

        // Enter the leftmost leaf containing a zero
        while v < leaves {
            increments += self.nodes[v].increment;
            v *= 2;
            if increments + self.nodes[v].minimum != 0 {
                v += 1;
            }
        }

        let index = v - leaves;
        (index < range.end).then_some(index)
    }

    pub fn add_segment(&mut self, range: Range<usize>) {
        // Increment the "covered by" counter for every gap within the range.
        self.range_increment(range.start + 1..range.end, 1);
    }

    pub fn remove_segment(&mut self, range: Range<usize>) {
        self.range_increment(range.start + 1..range.end, -1);
    }

    /// Returns the index of the first gap nested strictly within `range` not covered by any
    /// segments, if present.
    pub fn first_gap(&self, range: Range<usize>) -> Option<usize> {
        self.first_zero(range.start + 1..range.end)
    }
}
