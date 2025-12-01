use super::{Arena, ExprId};
use core::fmt;

pub trait DebugIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result;
}

impl<T: DebugIr + ?Sized> DebugIr for &T {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result {
        T::fmt(self, f, arena)
    }
}

impl DebugIr for ExprId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result {
        DebugIr::fmt(&arena[*self], f, arena)
    }
}
