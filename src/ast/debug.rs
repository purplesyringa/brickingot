use super::{Arena, ExprId};
use core::fmt;

pub trait DebugIr<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result;
}

impl<'code, T: DebugIr<'code> + ?Sized> DebugIr<'code> for &T {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        T::fmt(self, f, arena)
    }
}

impl<'code, T: DebugIr<'code>> DebugIr<'code> for Vec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        for stmt in self {
            writeln!(f, "{}", arena.debug(stmt))?;
        }
        Ok(())
    }
}

impl<'code> DebugIr<'code> for ExprId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        DebugIr::fmt(&arena[*self], f, arena)
    }
}
