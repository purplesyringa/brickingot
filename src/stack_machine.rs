use crate::arena::{Arena, ExprId};
use crate::ast::{BasicStatement, BinOp, Expression, PrimitiveType, VariableNamespace};
use crate::insn_stack_effect::{is_name_and_type_double_width, is_type_descriptor_double_width};
use crate::stackless::Statement;
use noak::{
    descriptor::{MethodDescriptor, TypeDescriptor},
    reader::cpool::value::NameAndType,
};
use thiserror::Error;

pub struct StackMachine<'arena, 'code> {
    pub arena: &'arena Arena<'code>,
    pub stack_size: usize,
}

#[derive(Debug, Error)]
#[error("Stack underflow")]
pub struct StackUnderflowError;

impl<'arena, 'code> StackMachine<'arena, 'code> {
    fn pop_sized(&mut self, size: usize) -> Result<ExprId, StackUnderflowError> {
        if self.stack_size < size {
            return Err(StackUnderflowError);
        }
        self.stack_size -= size;
        Ok(self.arena.alloc(Expression::Variable {
            id: self.stack_size,
            namespace: VariableNamespace::Stack,
        }))
    }

    pub fn pop(&mut self) -> Result<ExprId, StackUnderflowError> {
        self.pop_sized(1)
    }

    pub fn pop2(&mut self) -> Result<ExprId, StackUnderflowError> {
        self.pop_sized(2)
    }

    pub fn pop_method_arguments(
        &mut self,
        method_descriptor: &MethodDescriptor<'code>,
    ) -> Result<Vec<ExprId>, StackUnderflowError> {
        let parameter_sizes: Vec<usize> = method_descriptor
            .parameters()
            .map(|ty| {
                if is_type_descriptor_double_width(&ty) {
                    2
                } else {
                    1
                }
            })
            .collect();
        Ok(parameter_sizes
            .iter()
            .rev()
            .map(|size| self.pop_sized(*size))
            .collect::<Result<_, _>>()?)
    }

    pub fn pop_nat(
        &mut self,
        name_and_type: &NameAndType<'code>,
    ) -> Result<ExprId, StackUnderflowError> {
        if is_name_and_type_double_width(name_and_type) {
            self.pop2()
        } else {
            self.pop()
        }
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    fn push_sized(&mut self, size: usize, value: ExprId) -> Statement {
        let id = self.stack_size;
        self.stack_size += size;
        Statement::Basic(BasicStatement::Assign {
            target: self.arena.alloc(Expression::Variable {
                id,
                namespace: VariableNamespace::Stack,
            }),
            value,
        })
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    pub fn push(&mut self, value: ExprId) -> Statement {
        self.push_sized(1, value)
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    pub fn push2(&mut self, value: ExprId) -> Statement {
        self.push_sized(2, value)
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    pub fn push_return_type(
        &mut self,
        return_type: &Option<TypeDescriptor<'code>>,
        value: ExprId,
    ) -> Statement {
        if let Some(ret) = return_type {
            if is_type_descriptor_double_width(ret) {
                self.push2(value)
            } else {
                self.push(value)
            }
        } else {
            Statement::Basic(BasicStatement::Calculate(value))
        }
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    pub fn push_nat(&mut self, name_and_type: &NameAndType<'code>, value: ExprId) -> Statement {
        if is_name_and_type_double_width(name_and_type) {
            self.push2(value)
        } else {
            self.push(value)
        }
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    pub fn cast_primitive(
        &mut self,
        from: PrimitiveType,
        to: PrimitiveType,
    ) -> Result<Statement, StackUnderflowError> {
        let value = self.pop_sized(from.size())?;
        Ok(self.push_sized(
            to.size(),
            self.arena
                .alloc(Expression::CastPrimitive { value, from, to }),
        ))
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    pub fn binop(
        &mut self,
        op: BinOp,
        res_ty: PrimitiveType,
        lhs_ty: PrimitiveType,
        rhs_ty: PrimitiveType,
    ) -> Result<Statement, StackUnderflowError> {
        let rhs = self.pop_sized(rhs_ty.size())?;
        let lhs = self.pop_sized(lhs_ty.size())?;
        Ok(self.push_sized(
            res_ty.size(),
            self.arena.alloc(Expression::BinOp { lhs, rhs, op }),
        ))
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    pub fn arith_binop(
        &mut self,
        op: BinOp,
        ty: PrimitiveType,
    ) -> Result<Statement, StackUnderflowError> {
        self.binop(op, ty, ty, ty)
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    pub fn assign(&mut self, target: usize, value: ExprId) -> Statement {
        Statement::Basic(BasicStatement::Assign {
            target: self.at(target),
            value,
        })
    }

    pub fn at(&mut self, position: usize) -> ExprId {
        self.arena.stack(position)
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    pub fn copy(&mut self, target: usize, source: usize) -> Statement {
        let value = self.at(source);
        self.assign(target, value)
    }
}
