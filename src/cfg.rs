use crate::arrows::{Arrow, ArrowKind, extend_arrows};
use crate::unstructured;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum StructurizationError {}

pub fn structurize_cfg(program_in: unstructured::Program<'_>) -> Result<(), StructurizationError> {
    // Arrows are ordered pairs `(x, y)`, written `x -> y` or `y <- x`, indicating "travelling"
    // between gaps. A gap is the space between two statements; the index of a gap is the index of
    // the statement immediately following it. The presence of an arrow `x -> y` indicates that
    // there needs to be a way to travel from any statement between gaps `x` and `y` (or `y` and
    // `x`) to the gap `y`. Travelling from gap `x` to gap `x + 1` is implicitly allowed.
    //
    // Our current goal is to collect the arrows, which succinctly represent a linearized CFG. We
    // will then apply certain transforms (mostly elongating tails and splitting arrows into two) to
    // ensure they form a tree (i.e. any two arrows are either nested or don't intersect), which
    // we'll then turn into an AST.

    let mut arrows = Vec::new();

    let mut add_branch = |mut from: usize, to: usize, inner_index: usize| {
        let kind = ArrowKind::Jump {
            stmt_index: from,
            inner_index,
        };
        // If `from < to`, the statement `from` is within `[from; to)`. But if `from >= to`, `from`
        // is only present within `[to; from + 1)`, so we need to increment `from` so that the gap
        // interval covers the statement.
        if from >= to {
            from += 1;
        }
        arrows.push(Arrow { from, to, kind });
    };

    for (index, stmt) in program_in.statements.iter().enumerate() {
        match stmt {
            unstructured::Statement::Basic(_) => {}
            unstructured::Statement::Jump { target, .. } => add_branch(index, *target, 0),
            unstructured::Statement::Switch(unstructured::Switch {
                successors,
                default,
                ..
            }) => {
                for (i, (_, successor)) in successors.iter().enumerate() {
                    add_branch(index, *successor, i + 1);
                }
                add_branch(index, *default, 0);
            }
            unstructured::Statement::Catchpad => {}
        }
    }

    // Exception handlers also affect control flow: we need to be able to travel from any statement
    // within the `try` block to the exception handler. This is a little harder than it seems,
    // because adding the minimal arrow containing the guarded statements does not guarantee that we
    // can wrap the corresponding statements in a single `try` block.
    //
    // Consider, for example, the following input program:
    //
    //     print a;            \                                        |   : :
    //     if (...) goto 1;    | try { ... } catch { goto 2; }          | | : :
    //     print b;            /                                        | | : :
    //     goto 3;                                                      | v | :
    // 1:  print c;                                                     |   | :
    //     goto 3;                                                      v   | |
    // 2:  print d;                                                         v v
    // 3:
    //
    // ...which is a variant of the following snippet, just with messier control flow:
    //
    //     try {
    //         print a;
    //         if (...) print c; else print b;
    //     } catch {
    //         print d;
    //     }
    //
    // The trivial arrows here would be as marked on the right with the symbols `|` and `v`, which
    // will then be extended by `:` (dotted) to maintain nestedness.
    //
    // Cruicially, a `try` block *cannot* be added around the first three statements because it
    // would get interleaved with the second arrow (corresponding to the conditional jump). This is
    // because the arrow corresponding to the `try` block -- the first one -- actually captures the
    // first 6 statements, which would correspond to the following decompilation, at least after
    // a good optimization pass:
    //
    //     boolean is_in_range = true;
    //     try {
    //         print a;
    //         if (...) {
    //             is_in_range = false;
    //             print c;
    //         } else {
    //             print b;
    //         }
    //     } catch {
    //         if (!is_in_range) rethrow;
    //         print d;
    //     }
    //
    // Such arrows are *sufficient* for AST to be built because we can always simply wrap each
    // statement in an individual `try`..`catch` block with `goto` to the handler inside each
    // `catch` -- with `goto` being reducible because we're within the range of the arrow.
    for (handler_index, handler) in program_in.exception_handlers.iter().enumerate() {
        let to = handler.target;
        let kind = ArrowKind::Try { handler_index };
        if handler.target >= handler.end {
            arrows.push(Arrow {
                from: handler.start,
                to,
                kind,
            });
        } else if handler.target < handler.start {
            arrows.push(Arrow {
                from: handler.end,
                to,
                kind,
            });
        } else {
            // target within [start; end), incredibly cursed, need to split into two `try`s.
            // Alternatively, we could keep a single `try` and then jump to the handler from within
            // `catch`, but that gets quite messy. A naive set of two chained arrows produces
            // hypothetical code like:
            //
            //     try {
            //         a;
            //     handler:
            //         b;
            //     } catch {
            //         goto handler;
            //     }
            //
            // ...but we *can't* jump across blocks, and we haven't indicated to the arrows that the
            // jump from `catch` happens from after the end of the `try` block. We could insert
            // a fake statement, e.g.:
            //
            //     a            |
            //     b            v ^
            //     fake           |
            //
            // but those arrows would be extended via a dispatcher to:
            //
            //     dispatcher   | ^ |
            //     a            | | v
            //     b            v |
            //     fake           |
            //
            // which corresponds to code:
            //
            //     int selector = 0;
            //     while (true) {
            //         try {
            //             if (selector == 0) {
            //                 a;
            //             }
            //             b;
            //             break;
            //         } catch {
            //             selector = 1;
            //         }
            //     }
            //
            // which is more complicated and slower than the two-`try` version:
            //
            //     try {
            //         a;
            //     } catch {}
            //     while (true) {
            //         try {
            //             b;
            //             break;
            //         } catch {}
            //     }
            arrows.push(Arrow {
                from: handler.start,
                to,
                kind: kind.clone(),
            });
            arrows.push(Arrow {
                from: handler.end,
                to,
                kind,
            });
        }
    }

    // We now wish to extend arrows to turn the arrow set into a tree. The following paper forms the
    // basis for our algorithm -- feel free to read it, although we'll describe the main details
    // below:
    //
    //     Lyle Ramshaw. 1988. Eliminating go to's while preserving program structure.
    //     J. ACM 35, 4 (Oct. 1988), 893–920. https://doi.org/10.1145/48014.48021
    //
    // Our main goal is to get rid of conflicts, i.e. intersecting arrows. The intersecting parts of
    // the arrows can be either heads or tails independently, forming four categories of conflicts:
    // forward (both arrows pointed downward), backward (both pointer upward), tail-to-tail
    // (conflicting via tails), and head-to-head.
    //
    // The paper proves that all but head-to-head conflicts can be resolved by elongating arrow
    // tails. Such an operation only increases the set of allowed movements, and is thus lossless.
    //
    // Head-to-head conflicts, however, cannot be resolved by elongation, and it can be proven that
    // a "zero-cost" is impossible. We use a novel (or at least one that's not explicitly described
    // in literature) non-zero-cost solution instead: dispatchers. Conflicts are handled by
    // stretching the head of the backwards-pointing arrow to the tail of the forward arrow, and
    // then adding another forward arrow to return to the correct position. (In this diagram,
    // statements are oriented to the right rather than downwards for brevity.)
    //
    //     ----------------->              normal jump
    //               <--------------
    //
    //                  ||
    //                  vv
    //
    //     ----------------->              normal jump
    //     <------------------------       jump to dispatcher
    //     --------->                      dispatch
    //
    // Immediately before the statement the "jump to dispatcher" arrow points to, a *dispatcher* is
    // inserted. The dispatcher reads a synthetic local variable, called *selector*, and either
    // jumps to one of the arrow heads, or skips to the next statement depending on its value. The
    // selector is assigned at the end of each predecessor of the dispatcher.
    //
    // This is kind of like a state machine, but a local one. If one part of a large function
    // contains irreducible control flow, we don't rewrite the entier function to use a state
    // machine, we minimize the impact.

    extend_arrows(&mut arrows);
    println!("{arrows:?}");

    /*
    // After collecting the arrows, we will extend certain arrows as little as possible such that
    // the arrows form a tree (i.e.: any two errors are either nested or don't intersect), and all
    // the travelling restrictions are still met (so while we can easily extend tails, extending
    // heads is more complex and requires adding new auxiliary arrows).
    //
    // Such a tree forms the basis for the AST. An up-arrow (i.e. from a later statement to
    // an earlier one) can be translated to `while (true) { ... break; }`, and jumping to the head
    // of such an arrow can be implemented with a (multi-level) `continue`. Similarly, a down-arrow
    // can be implemented with `do { ... } while (false);`, with `break` being used for jumping.
     */

    Ok(())
}
