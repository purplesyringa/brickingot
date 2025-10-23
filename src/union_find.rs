pub struct UnionFind {
    // If `x >= 0`, it's the parent ID. If `x < 0`, it's `-rank`.
    parents_or_ranks: Vec<i32>,
}

impl UnionFind {
    pub fn new(len: u32) -> Self {
        Self {
            parents_or_ranks: vec![-1; len as usize],
        }
    }

    pub fn merge(&mut self, mut a: u32, mut b: u32) {
        a = self.resolve(a);
        b = self.resolve(b);
        if a == b {
            return;
        }

        let rank_a = self.parents_or_ranks[a as usize];
        let rank_b = self.parents_or_ranks[b as usize];
        if rank_a > rank_b {
            core::mem::swap(&mut a, &mut b);
        } else if rank_a == rank_b {
            self.parents_or_ranks[a as usize] -= 1;
        }
        self.parents_or_ranks[b as usize] = a as i32;
    }

    pub fn resolve(&mut self, mut index: u32) -> u32 {
        let mut leader = index;
        while self.parents_or_ranks[leader as usize] >= 0 {
            leader = self.parents_or_ranks[leader as usize] as u32;
        }
        while index != leader {
            index = core::mem::replace(&mut self.parents_or_ranks[index as usize], leader as i32)
                as u32;
        }
        leader
    }

    pub fn is_unique(&self, index: u32) -> bool {
        self.parents_or_ranks[index as usize] == -1
    }
}
