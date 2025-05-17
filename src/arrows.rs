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
    // arrows, and then resolution will work correctly:
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
        if let Some((min, max)) = stack.last_mut()
            && *max > arrow_min
        {
            *max = arrow_max;
            if arrow.to > arrow.from {
                arrow.from = *min;
            }
        } else {
            stack.push((arrow_min, arrow_max));
        }
    }

    // Stage 3. We again perform a sweeping line approach, but a trickier one than before.
    //
    // The main problem here is ensuring that adding the dispatcher arrow doesn't introduce any new
    // conflicts, or at least any head-to-head conflicts among the set of already handled arrows.
    // The simplest counter-example is
    //
    //          ------------->
    //     ---------------------------->
    //                 <-----------
    //             <-------------------------
    //
    // ...where, if the shorter upward arrow is handled first, the longer upward arrow gets two
    // conflicts -- a backward one with the longer upward arrow and a head-to-head conflict with
    // the dispatch arrow:
    //
    //          ------------->
    //     ---------------------------->
    //          <------------------
    //          ------>
    //             <-------------------------
    //
    // Because of the backward conflict, attempting to resolve the head-to-head conflict will then
    // result in a situation where not just a *forward* conflict happens between dispatch arrows
    // (which is already a bad thing because elongating the dispatch arrow would require moving the
    // dispatcher, but that would also mean the arrow pointing *into* the dispatcher needs its head
    // moved), but also a *head-to-head* conflict is introduced between the new dispatch arrow and
    // the old upward arrow:
    //
    //          ------------->
    //     ---------------------------->
    //          <------------------
    //          ------>
    //     <---------------------------------
    //     ------->
    //
    // We must therefore handle arrows in such an order that similar head-to-head cannot be ever
    // introduced, and that requires us to handle the outmost upward arrow first, which results
    // exclusively in a forward conflict, where only the non-dispatch arrow arrow needs to be
    // extended:
    //
    //          ------------->
    //     ---------------------------->
    //     <---------------------------------
    //     ------->
    //     <-----------------------
    //     ----------->
    //
    // We formalize this approach by handling arrows in the order of their *minimal* coordinates,
    // which complicates the sweeping line code, but avoids this problem.
    //
    // Here's the general approach. It mostly mirrors the approach from the previous stages, but the
    // details are tricky, so let's formalize it.
    // - We're moving arrows from the set of unhandled arrows to the set of handled arrows one by
    //   one in the order of minimal coordinates. We maintain an auxiliary data structure on the set
    //   of handled arrows.
    // - We do not *commit* certain changes to arrows. In particular, the output may contain
    //   unresolved forward conflicts (and *only* forward conflicts). Those conflicts will be
    //   resolved on stage 4. However, the auxiliary data structure is built on the hypothetical
    //   arrow set where those conflicts have already been resolved. In other words, the output
    //   containing conflicts is merely an optimization that enables us to patch the already
    //   outputted data when older arrows are modified (but the auxiliary structure still needs to
    //   be updated).
    //
    // An arriving upward arrow `a <- b` can only have a head-to-head conflict with already handled
    // arrows `* -> c`, where `a < c < b`. We don't need to keep track of `*` because it's
    // guaranteed to be `< a` due to scan order (`<=`, actually, so we need to nudge the sorting
    // order a bit). There can be multiple such arrows, all nested:
    //
    //      ----------------->  (1)
    //       ------------->     (2)
    //          -------->       (3)
    //               <-------   collides with (2) and (3), but not (1)
    //
    // There can also be arrows in the tree "to the left" of the arrows in the diagram, which we
    // cannot collide with, but no arrows "to the right".
    //
    // To resolve such a conflict, we find the outmost arrow we collide with and extend our head to
    // its tail:
    //
    //      ----------------->
    //       ------------->
    //          -------->
    //       <---------------
    //       ------->
    //
    // This will, in turn, create forward conflicts with nested arrows, (3) in this case. We will
    // resolve this conflict implicitly, but not patch the output, because there could be a linear
    // number of such arrows:
    //
    //      ----------------->
    //       ------------->
    //       ----------->
    //       <---------------
    //       ------->
    //
    // To see why dispatcher arrows cannot be extended during this forward conflict resolution,
    // notice that the minimum coordinates of all further inputs are greater than the dispatcher's
    // head, meaning that it won't be interacted with.
    //
    // When a downward arrow `a -> b` arrives, we know for a fact that it can't have a forward
    // conflict with any existing arrow, because all existed arrows have been added when they had
    // minimal coordiantes `< a`, meaning that there must have already been a forward conflict in
    // the input for this to happen.
    //
    // For our auxiliary data structure, we could store a stack of nested downward arrows; this is
    // effectively the set of arrows obtained by travelling downward from the tree root if, at each
    // point we only visit the rightmost child. This is trivial to populate, but we also need to
    // handle transforms like this one:
    //
    //     ------------------------>                ------------------------>   \
    //        ----------------->        ===>           ----------------->       |  data structure
    //           ----------->                          -------------->          |
    //            ----->                               --------->               /
    //              <-------------                           <-------------     <- query
    //
    // In effect, this is a mass-update query on a tail of the stack. It does not allow us to
    // *remove* the updated elements from the stack, meaning that they may also be accessed on the
    // later iterations, bumping complexity to quadratic. But there's a fix.
    //
    // Updating arrows like this can be seen as merging them together. Let's separate the stack into
    // two: one stack will store heads of arrows, while another will store groups of tails of those
    // same arrows. Handling the query then requires us to merge some elements of the "group" stack
    // together, which we can do in O(1) amortized.
    //
    // Crucially, the absence of backward conflicts in the input guarantees that any arrow that has
    // been extended during this stage won't ever be extended in this fashion again.
    //
    // We'll need to push into `arrows`, so the iteration is a bit unidiomatic.
    arrows.sort_by_key(|arrow| (arrow.from.min(arrow.to), Reverse(arrow.from.max(arrow.to))));
    let mut heads_stack: Vec<usize> = Vec::new();
    // Reusing an allocation like this just because the types match (`(start index, tail)` in this
    // case) is... questionable, but it's fiiiiiiiine, don't worry. :)
    let mut tails_stack = stack;
    tails_stack.clear();
    for i in 0..arrows.len() {
        let arrow = &mut arrows[i];
        let arrow_min = arrow.from.min(arrow.to);
        while heads_stack.pop_if(|head| *head <= arrow_min).is_some() {}
        while tails_stack
            .pop_if(|(start, _)| *start >= heads_stack.len())
            .is_some()
        {}
        if arrow.to > arrow.from {
            tails_stack.push((heads_stack.len(), arrow.from));
            heads_stack.push(arrow.to);
        } else {
            if heads_stack.last().is_none_or(|head| *head >= arrow.from) {
                continue;
            }
            while tails_stack
                .pop_if(|(start, _)| *start > 0 && heads_stack[*start - 1] < arrow.from)
                .is_some()
            {}
            let tail = tails_stack.last().unwrap().1;
            let to = arrow.to;
            arrow.to = tail;
            arrows.push(Arrow {
                from: tail,
                to,
                kind: ArrowKind::Dispatch,
            });
        }
    }

    // Stage 4. This is effectively an optimized version of stage 2 that completely ignores upward
    // arrows. We need to re-sort because stage 3 can push new downward arrows.
    arrows.sort_by_key(|arrow| (arrow.to, Reverse(arrow.from)));
    let mut stack = tails_stack; // bring allocation back
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
    use rand::{RngCore, SeedableRng, rngs::SmallRng};
    use std::collections::HashSet;

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

    // Ensures that collisions are handled correctly with arrows in-between
    #[test]
    fn skips() {
        // ----------> --->
        //    --->  --------->
        test_arrows(
            &[(1, 5), (6, 7), (2, 3), (4, 8)],
            &[(1, 5), (6, 7), (2, 3), (1, 8)],
        );
        // <---------- --->
        //    --->  --------->
        test_arrows(
            &[(5, 1), (6, 7), (2, 3), (4, 8)],
            &[(5, 1), (6, 7), (2, 3), (1, 8)],
        );
        // <---------- <---
        //    <---  <---------
        test_arrows(
            &[(5, 1), (7, 6), (3, 2), (8, 4)],
            &[(8, 1), (7, 6), (3, 2), (8, 4)],
        );
        // ----------> --->
        //    --->  <---------
        test_arrows(
            &[(1, 5), (6, 7), (2, 3), (8, 4)],
            &[(1, 5), (6, 7), (2, 3), (8, 1), (1, 4)],
        );
    }

    // Tests that arrows with matching heads/tails are not overexpanded
    #[test]
    fn equal() {
        for small_is_first in [false, true] {
            for small_is_left in [false, true] {
                for small_is_downward in [false, true] {
                    for large_is_downward in [false, true] {
                        let mut first = (1, 3);
                        let mut second = if small_is_left { (1, 2) } else { (2, 3) };
                        if large_is_downward {
                            core::mem::swap(&mut first.0, &mut first.1);
                        }
                        if small_is_downward {
                            core::mem::swap(&mut second.0, &mut second.1);
                        }
                        if small_is_first {
                            core::mem::swap(&mut first, &mut second);
                        }
                        test_arrows(&[first, second], &[first, second]);
                    }
                }
            }
        }
    }

    // Non-trivial examples from comments in `extend_arrows`
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

    // Counter-examples found by stress test
    #[test]
    fn counterexamples() {
        // Non-trivial head-to-head conflicts
        test_arrows(
            &[(1, 4), (0, 6), (5, 3), (7, 2)],
            &[(0, 4), (0, 6), (5, 0), (7, 0), (0, 2), (0, 3)],
        );

        // Stack order in head-to-head conflict resolution (ensures `.rev()` is not missed)
        test_arrows(
            &[(5, 2), (0, 8), (0, 4), (0, 7), (9, 1)],
            &[(5, 0), (0, 8), (0, 4), (0, 7), (9, 0), (0, 1), (0, 2)],
        );

        // Broken forward conflict resolution
        test_arrows(
            &[(9, 7), (1, 6), (0, 3), (5, 2), (1, 8)],
            &[(9, 0), (0, 6), (0, 3), (5, 0), (0, 8), (0, 2), (0, 7)],
        );
    }

    #[test]
    fn stress() {
        let mut rng = SmallRng::seed_from_u64(1);

        for step in 0..100000 {
            let mut arrows: [_; 7] =
                core::array::from_fn(|_| (rng.next_u32() as usize, rng.next_u32() as usize));

            if step % 3 == 0 {
                // Test aliasing edges
                for (from, to) in &mut arrows {
                    *from &= 15;
                    *to &= 15;
                }
                if arrows.iter().any(|(from, to)| from == to) {
                    continue;
                }
            }

            let mut expanded_arrows = arrows
                .iter()
                .enumerate()
                .map(|(i, &(from, to))| Arrow {
                    from,
                    to,
                    kind: ArrowKind::Try { handler_index: i },
                })
                .collect();

            extend_arrows(&mut expanded_arrows);

            expanded_arrows.sort_by_key(|arrow| match arrow.kind {
                ArrowKind::Try { handler_index } => handler_index,
                ArrowKind::Dispatch => usize::MAX,
                _ => unreachable!(),
            });

            let dispatches: HashSet<(usize, usize)> = expanded_arrows[arrows.len()..]
                .iter()
                .map(|expanded_arrow| {
                    assert_eq!(
                        expanded_arrow.kind,
                        ArrowKind::Dispatch,
                        "non-dispatch arrow",
                    );
                    assert!(
                        expanded_arrow.from < expanded_arrow.to,
                        "non-downward dispatch",
                    );
                    (expanded_arrow.from, expanded_arrow.to)
                })
                .collect();

            for (i, (arrow, expanded_arrow)) in arrows.iter().zip(&expanded_arrows).enumerate() {
                assert_eq!(
                    expanded_arrow.kind,
                    ArrowKind::Try { handler_index: i },
                    "wrong arrow kind",
                );
                let is_expansion = if arrow.0 < arrow.1 {
                    expanded_arrow.from <= arrow.0 && arrow.1 == expanded_arrow.to
                } else {
                    if expanded_arrow.to < arrow.1 {
                        assert!(
                            dispatches.contains(&(expanded_arrow.to, arrow.1)),
                            "not able to dispatch {} -> {}",
                            expanded_arrow.to,
                            arrow.1,
                        );
                    }
                    expanded_arrow.from >= arrow.0 && arrow.1 >= expanded_arrow.to
                };
                assert!(is_expansion, "not an expansion");
            }

            expanded_arrows
                .sort_by_key(|arrow| (arrow.from.max(arrow.to), Reverse(arrow.from.min(arrow.to))));
            let mut stack = Vec::new();
            for arrow in expanded_arrows {
                let arrow_min = arrow.from.min(arrow.to);
                let arrow_max = arrow.from.max(arrow.to);
                while stack.pop_if(|(min, _)| *min >= arrow_min).is_some() {}
                if let Some((_, max)) = stack.last() {
                    assert!(*max <= arrow_min, "non-nested arrows in output");
                }
                stack.push((arrow_min, arrow_max));
            }
        }
    }
}
