use crate::ast::{Expression, VariableNamespace};
use core::fmt::{self, Display};
use core::ops::{Index, IndexMut};

#[derive(Clone, Copy, Debug)]
pub struct ExprId(u32);

pub struct Arena<'code> {
    elements: boxcar::Vec<Expression<'code>>,
}

impl<'code> Arena<'code> {
    pub fn new() -> Self {
        Self {
            elements: boxcar::Vec::new(),
        }
    }

    pub fn alloc(&self, expr: Expression<'code>) -> ExprId {
        ExprId(
            self.elements
                .push(expr)
                .try_into()
                .expect("expression ID overflow"),
        )
    }

    pub fn stack(&self, id: usize) -> ExprId {
        self.alloc(Expression::Variable {
            id,
            namespace: VariableNamespace::Stack,
        })
    }

    pub fn slot(&self, id: usize) -> ExprId {
        self.alloc(Expression::Variable {
            id,
            namespace: VariableNamespace::Slot,
        })
    }

    pub fn tmp(&self, id: usize) -> ExprId {
        self.alloc(Expression::Variable {
            id,
            namespace: VariableNamespace::Temporary,
        })
    }

    pub fn int(&self, value: i32) -> ExprId {
        self.alloc(Expression::ConstInt(value))
    }

    pub fn null(&self) -> ExprId {
        self.alloc(Expression::Null)
    }

    pub fn debug<'a, T: DebugIr<'code> + ?Sized>(&'a self, value: &'a T) -> impl Display {
        struct IrDisplay<'a, 'code, T: ?Sized> {
            value: &'a T,
            arena: &'a Arena<'code>,
        }

        impl<'a, 'code, T: DebugIr<'code> + ?Sized> Display for IrDisplay<'a, 'code, T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                T::fmt(self.value, f, self.arena)
            }
        }

        IrDisplay { value, arena: self }
    }
}

impl<'code> Index<ExprId> for Arena<'code> {
    type Output = Expression<'code>;

    fn index(&self, id: ExprId) -> &Self::Output {
        &self.elements[id.0 as usize]
    }
}

impl<'code> IndexMut<ExprId> for Arena<'code> {
    fn index_mut(&mut self, id: ExprId) -> &mut Self::Output {
        self.elements
            .get_mut(id.0 as usize)
            .expect("non-existing expression ID")
    }
}

pub trait DebugIr<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result;
}

impl<'code, T: DebugIr<'code> + ?Sized> DebugIr<'code> for &T {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        T::fmt(self, f, arena)
    }
}

impl<'code> DebugIr<'code> for ExprId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        DebugIr::fmt(&arena[*self], f, arena)
    }
}
