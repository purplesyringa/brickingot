mod inlining;
mod main_opt;

use self::main_opt::optimize;
use crate::ast::{Arena, IrDef, NoMeta, StmtList};
use crate::exceptions;
use alloc::fmt;

pub struct Ir;

impl IrDef for Ir {
    type Meta = Meta;
    type BasicMeta = NoMeta;
    type BlockMeta = NoMeta;
    type ContinueMeta = NoMeta;
    type BreakMeta = NoMeta;
    type IfMeta = IfMeta;
    type SwitchMeta = NoMeta;
    type TryMeta = NoMeta;
    type CatchMeta = crate::ast::NoMeta;
}

pub type Program = StmtList<Ir>;

#[derive(Debug)]
pub struct IfMeta {
    // We use this to reorder statements closer to source without patching `condition`, since we may
    // need to invert it multiple times, and flicking a bool is simpler.
    condition_inverted: bool,
}

impl fmt::Display for IfMeta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.condition_inverted {
            write!(f, "inverted ")?;
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct Meta {
    is_divergent: bool,
    first_uninlined_switch_arm: usize,
    n_breaks_from_switch: usize,
}

impl fmt::Display for Meta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_divergent {
            write!(f, "!divergent ")?;
        }
        Ok(())
    }
}

pub fn decompile_cf_constructs<'code>(
    arena: &mut Arena<'code>,
    eh_ir: exceptions::Program,
) -> Program {
    // The general approach here is to consider a high-level Java control flow construct, find the
    // properties that all of its lowerings are guaranteed to have, and tweak them such that either
    // there are no false positive matches, or all false positives are documented and can be
    // accounted for.

    // Perhaps the most important problem during this stage is determining whether a sequence of
    // statements can be simplified to a single expression. This is necessary to recognize
    // conditions of `while` loops, to translate `if` into `?:` (which in turn determines whether
    // other sequences can be simplified), and to handle `&&`/`||` chains.
    //
    // We perform the bulk of the work necessary to answer this question in a single pass. This
    // includes decompiling `if` statements and Java features lowering to loops, like `switch`
    // expressions with guarded patterns. It also allows us not to think too hard about fixpointing
    // and making sure earlier passes don't make possibly suboptimal decisions that might impact
    // later passes.
    //
    // The above implies that this pass must convert statements into a single `Assign` if that's
    // possible; but if it's not, basically no requirements are made regarding the pass output. This
    // allows unused blocks, no-op `break`/`continue`, etc., which are hard to fix up in a single
    // pass efficiently.
    optimize(arena, eh_ir)
}
