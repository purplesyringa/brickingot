use core::cmp::Reverse;

#[derive(Clone, Debug, PartialEq)]
pub enum ArrowKind {
    Jump {
        stmt_index: usize,
        inner_index: usize, // for switch
    },
    Try {
        handler_index: usize,
    },
    Dispatch,
}

#[derive(Debug, PartialEq)]
pub struct Arrow {
    pub from: usize,
    pub to: usize,
    pub kind: ArrowKind,
}

pub fn extend_arrows(arrows: &mut Vec<Arrow>) {
    // Check out the comments in `cfg.rs` for exactly what we're doing here. In a nutshell, given
    // a couple of arrows, we want to extend some of them (preferably tails, but occasionally heads
    // too) such that the result has no conflicts, i.e. arrows that intersect but are not nested.
    //
    // While we could obviously extend each arrow to the boundaring range, that would lead to
    // suboptimal codegen, so we want to minimize the extension in some sense. Extending tails is
    // cheaper in this sense than extending heads (which can also only be extended upwards/to the
    // left), and we need to avoid introducing new collisions during the process if possible.
    //
    // Our implementation is more difficult than the one in Lyle Ramshaw's paper because we want to
    // keep the complexity quasi-linear (to be precise, it's linear except for sorting). Our
    // algorithm is composed of the following stages:
    //
    // 1. Resolve backward conflicts without introducing head-to-head conflicts if there weren't
    //    any.
    // 2. Resolve forward and tail-to-tail conflicts while introducing neither head-to-head
    //    conflicts if there weren't any beforehand, nor backward conflicts.
    // 3. Resolve head-to-head conflicts at the cost of introducing only forward conflicts.
    // 4. Resolve forward conflicts without introducing any conflicts.
    //
    // ...where each stage relies on the previous one for correctness.

    // In the diagrams below, arrow pointing to the right are considered to be downward/forward
    // arrows, and arrows pointing to the left are upward/backward arrows.

    // Stage 1. We add upward arrows one by one in a sweeping line, ordered by their head
    // coordinate. Downward arrows are ignored/unaffected.
    //
    // We ensure that there's no backward conflicts among already handled arrows at any point, not
    // just at the end of the stage. This guarantees that if a new arrow A has backward conflicts
    // with B and C, then B and C are nested, so we only need to resolve the conflict with the outer
    // arrow. This list of non-intersecting outer upward arrows can be easily manipulated when
    // stored in a stack.
    //
    // It's easy to see that elongating the tail can only introduce head-to-head conflicts in the
    // following situation:
    //
    //     --------------->
    //         <-------
    //            <---------------
    //
    //              ||
    //              vv
    //
    //     --------------->
    //         <-------- - - - - -
    //            <---------------
    //
    // ...where a head-to-head conflict has already been present between another pair of arrows.
    arrows.sort_by_key(|arrow| (Reverse(arrow.to), arrow.from));
    let mut stack: Vec<(usize, usize)> = Vec::new();
    for arrow in &mut *arrows {
        if arrow.to < arrow.from {
            while stack.pop_if(|(from, _)| *from <= arrow.from).is_some() {}
            if let Some((from, _)) = stack.pop_if(|(_, to)| *to < arrow.from) {
                arrow.from = from;
            }
            stack.push((arrow.from, arrow.to));
        }
    }

    // Stage 2. We add *all* arrows in a sweeping line, but only fix up downward arrows.
    //
    // We ensure that there are no conflicts but head-to-head conflicts among the already handled
    // arrows at any point.
    //
    // A downward arrow needs to be fixed if its tail is within an already inserted arrow. If it's
    // located within two arrows A, B such that A is nested within B, A can be safely ignored,
    // which means that we only need to store the outmost arrows. However, unlike in the previous
    // stage, the presence of head-to-head conflicts means that arrows are not necessarily
    // non-intersecting, e.g. the following is a valid "history":
    //
    //     ---->          ----->
    //             <----     <-----
    // If a new arrow arrives at the following position:
    //                           ======>
    // its tail is only within the rightmost arrow, but extending it like this:
    //                       ==========>
    // means that it'll now be within the previous arrow as well, so it'll have to be further
    // extended like so:
    //                    =============>
    // So instead of storing arrows themselves in the stack, we can store unoriented unions of
    // arrows, and resolution will work correctly:
    //     -----   -----  ---------
    //
    // Clearly, backward conflicts cannot be introduced because we don't modify upward arrows. New
    // head-to-head conflicts can only appear in the following situation, where another head-to-head
    // conflict is already present:
    //
    //            <---------
    //      - - - - - ---->     (dashed part is added during this stage)
    //      ----------->
    arrows.sort_by_key(|arrow| (arrow.from.max(arrow.to), Reverse(arrow.from.min(arrow.to))));
    stack.clear();
    for arrow in &mut *arrows {
        let arrow_min = arrow.from.min(arrow.to);
        let arrow_max = arrow.from.max(arrow.to);
        while stack.pop_if(|(min, _)| *min >= arrow_min).is_some() {}
        if arrow.to > arrow.from {
            if let Some((min, _)) = stack.pop_if(|(_, max)| *max > arrow_min) {
                // Notably, this assignment doesn't invalidate the sorting order, which allows us to
                // avoid re-sorting on stage 3.
                arrow.from = min;
            }
        } else {
            if let Some((_, max)) = stack.last_mut()
                && *max > arrow_min
            {
                *max = arrow_max;
                continue;
            }
        }
        stack.push((arrow_min, arrow_max));
    }

    // Stage 3. We again perform a sweeping line approach.
    //
    // We maintain that:
    // - There are only forward conflicts among the already handled arrows.
    // - There are only head-to-head conflicts among arrows that haven't yet been handled.
    // - There are only head-to-head and certain backward conflicts between arrows that have and
    //   haven't been handled.
    //
    // When an upward arrow arrives, we need to find downward arrows containing the arrival's head.
    // Arrows nested within other arrows are unnecessary to track, but note that there can still be
    // forward conflicts:
    //     --------->
    //         -------->
    //           <---------------
    // To resolve both conflicts, we need to extend the head until the tail of the first arrow (and
    // add the corresponding dispatch arrow):
    //     --------->
    //         -------->
    //     <---------------------
    //     ----->
    // ...and that holds even if the original picture looked like this:
    //     --------->
    //         -------->
    //                <----------
    // ...so we need to track the union of the downward arrows.
    //
    // We've used a stack for operations like this one so far, but it breaks down because an input
    // like
    //     ---->    ---->    ---->    --->
    //                <-----------------------
    // requires us to retrieve an element below the top of the stack without removing everything
    // above it, which is not something we can do as efficiently. But not all hope is lost: the
    // elements above the retrieved one could only be useful to an input like
    //     ---->    ---->    ---->    --->
    //                <-----------------------
    //                         <------------------
    // ...but the input of this stage doesn't contain backward conflicts, which means we can safely
    // remove those elements.
    //
    // The other major pain here is a situation like this:
    //     ------------>
    //             <----------
    //          <------------------
    // The smaller head-to-head collision will be resolved first, producing the following arrows:
    //     ------------>
    //     <------------------          \
    //     ------->                      - backward conflict
    //          <------------------     /
    // This is the only case when a backward conflict can be introduced, and that complicates
    // things, but this conflict will automatically disappear when the larger head-to-head collision
    // is resolved:
    //     ------------>
    //     <------------------
    //     ------->
    //     <-----------------------
    //     ---->
    // ...so this is only temporary.
    //
    // That's the only conflict that elongating the arrow can introduce, but we also need to
    // consider the dispatcher arrow. A forward conflict can be introduced in the following case:
    //     ------------->
    //            <----------
    //         ------>
    // (after:)
    //     ------------->
    //     <-----------------
    //     ------>
    //         ------>
    // ...which we'll handle on stage 4 (we can't handle it *now* because we'd have to touch already
    // processed arrows, and that could happen multiple times, increasing complexity to quadratic).
    // A *head-to-head* conflict can be introduced in the following case:
    //     ---------->
    //           <--------
    //        <-------------
    // (after:)
    //     ---------->
    //     <--------------
    //     ----->
    //        <-------------
    // But this is a conflict with a yet unhandled arrow, so it will be resolved when that arrow is
    // checked -- and that's not a "new" conflict in the sense that that arrow would have been fixed
    // up regardless.
    //
    // We'll need to push into `arrows`, so the iteration is a bit unidiomatic.
    stack.clear();
    for i in 0..arrows.len() {
        let arrow = &mut arrows[i];
        let arrow_min = arrow.from.min(arrow.to);
        while stack.pop_if(|(from, _)| *from >= arrow_min).is_some() {}
        if arrow.to > arrow.from {
            if let Some((_, to)) = stack.last_mut()
                && *to > arrow_min
            {
                *to = arrow.to;
            } else {
                stack.push((arrow.from, arrow.to));
            }
        } else {
            if let Some((from, to)) = stack.last_mut()
                && *to > arrow_min
            {
                arrow.to = *from;
                arrows.push(Arrow {
                    from: *from,
                    to: arrow_min,
                    kind: ArrowKind::Dispatch,
                });
            }
        }
    }

    // Stage 4. This is effectively an optimized version of stage 2 that completely ignores upward
    // arrows. We need to re-sort because stage 3 can push new downward arrows.
    arrows.sort_by_key(|arrow| (arrow.to, Reverse(arrow.from)));
    stack.clear();
    for arrow in &mut *arrows {
        if arrow.to > arrow.from {
            while stack.pop_if(|(from, _)| *from >= arrow.from).is_some() {}
            if let Some((from, _)) = stack.pop_if(|(_, to)| *to > arrow.from) {
                arrow.from = from;
            }
            stack.push((arrow.from, arrow.to));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_arrows(arrows: &[(usize, usize)], expected: &[(usize, usize)]) {
        let mut arrows = arrows
            .iter()
            .enumerate()
            .map(|(i, &(from, to))| Arrow {
                from,
                to,
                kind: ArrowKind::Try { handler_index: i },
            })
            .collect();

        extend_arrows(&mut arrows);

        arrows.sort_by_key(|arrow| match arrow.kind {
            ArrowKind::Try { handler_index } => handler_index,
            ArrowKind::Dispatch => usize::MAX,
            _ => unreachable!(),
        });

        let all_ok = arrows.len() == expected.len()
            && arrows
                .iter()
                .zip(expected)
                .all(|(arrow, expected)| (arrow.from, arrow.to) == *expected);
        if !all_ok {
            panic!("test failed\narrows: {arrows:?}\nexpected: {expected:?}");
        }
    }

    #[test]
    fn basic() {
        // No collisions
        test_arrows(&[], &[]);
        test_arrows(&[(1, 2), (3, 4)], &[(1, 2), (3, 4)]);
        test_arrows(&[(2, 1), (3, 4)], &[(2, 1), (3, 4)]);
        test_arrows(&[(1, 2), (4, 3)], &[(1, 2), (4, 3)]);
        test_arrows(&[(2, 1), (4, 3)], &[(2, 1), (4, 3)]);

        // Nested
        test_arrows(&[(1, 4), (2, 3)], &[(1, 4), (2, 3)]);
        test_arrows(&[(1, 4), (3, 2)], &[(1, 4), (3, 2)]);
        test_arrows(&[(4, 1), (2, 3)], &[(4, 1), (2, 3)]);
        test_arrows(&[(4, 1), (3, 2)], &[(4, 1), (3, 2)]);

        // Single collision
        // Forward
        test_arrows(&[(1, 3), (2, 4)], &[(1, 3), (1, 4)]);
        // Tail-to-tail; [(4, 1), (2, 4)] would be valid too
        test_arrows(&[(3, 1), (2, 4)], &[(3, 1), (1, 4)]);
        // Backward
        test_arrows(&[(3, 1), (4, 2)], &[(4, 1), (4, 2)]);
        // Head-to-head
        test_arrows(&[(1, 3), (4, 2)], &[(1, 3), (4, 1), (1, 2)]);
    }

    // Mostly examples from comments above, expanded
    #[test]
    fn interactions() {
        // ------------------->
        //     <-----------
        //         <-------------------
        // Can be manually translated by resolving the head-to-head collision first:
        // ------------------->
        //     <-----------
        // <---------------------------
        // ------->
        // ...and then resolving the new head-to-head collision:
        // ------------------->
        // <---------------
        // <---------------------------
        // ------->
        // --->
        // But *automatically*, this is first handled by resolving the backward collision:
        // ------------------->
        //     <-----------------------
        //         <-------------------
        // and then the two head-to-head collisions:
        // ------------------->
        // <---------------------------
        // <---------------------------
        // ------->
        // --->
        // That's not bad per se, because nested arrows with matching heads are cheap regardless of
        // the tail position, but `test_arrows` resolving a non-minimal solution is a non-obvious
        // implementation detail.
        test_arrows(
            &[(1, 5), (4, 2), (6, 3)],
            &[(1, 5), (6, 1), (6, 1), (1, 2), (1, 3)],
        );

        //            <---------
        //                ---->
        //      ----------->
        test_arrows(&[(6, 2), (3, 5), (1, 4)], &[(6, 1), (1, 5), (1, 4), (1, 2)]);

        //     --------->
        //         -------->
        //           <---------------
        test_arrows(&[(1, 4), (2, 5), (6, 3)], &[(1, 4), (1, 5), (6, 1), (1, 3)]);

        //     ---->    ---->    ---->    --->
        //                <-----------------------
        //                         <------------------
        test_arrows(
            &[(1, 2), (3, 5), (6, 8), (9, 10), (11, 4), (12, 7)],
            &[
                (1, 2),
                (3, 5),
                (6, 8),
                (9, 10),
                (12, 3),
                (12, 6),
                (3, 4),
                (6, 7),
            ],
        );

        //     ------------>
        //             <----------
        //          <------------------
        test_arrows(
            &[(1, 4), (5, 3), (6, 2)],
            &[(1, 4), (5, 1), (6, 1), (1, 2), (1, 3)],
        );

        //     ------------->
        //            <----------
        //         ------>
        test_arrows(&[(1, 5), (6, 3), (2, 4)], &[(1, 5), (6, 1), (1, 4), (1, 3)]);
    }
}
