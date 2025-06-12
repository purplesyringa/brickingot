use crate::arena::{Arena, ExprId};
use crate::ast::{
    BasicStatement, BinOp, Expression, PrimitiveType, VariableName, VariableNamespace,
};
use crate::insn_stack_effect::{is_name_and_type_double_width, is_type_descriptor_double_width};
use crate::stackless::Statement;
use noak::{
    descriptor::{MethodDescriptor, TypeDescriptor},
    reader::cpool::value::NameAndType,
};
use rustc_hash::FxHashMap;
use std::collections::hash_map::Entry;
use thiserror::Error;

pub struct ActiveDef {
    pub version: ExprId,
    // true if this entry corresponds to a fake definition used to link multiple unresolved uses
    // together.
    pub is_fake: bool,
}

pub struct Machine<'arena, 'code> {
    pub arena: &'arena Arena<'code>,
    pub stack_size: usize,
    pub active_defs: FxHashMap<VariableName, ActiveDef>,
    pub unresolved_uses: FxHashMap<VariableName, Vec<(usize, ExprId)>>,
    pub bb_id: usize,
    pub statements: Vec<Statement>,
}

#[derive(Debug, Error)]
#[error("Stack underflow")]
pub struct StackUnderflowError;

impl<'arena, 'code> Machine<'arena, 'code> {
    fn pop_sized(&mut self, size: usize) -> Result<ExprId, StackUnderflowError> {
        if self.stack_size < size {
            return Err(StackUnderflowError);
        }
        self.stack_size -= size;
        Ok(self.get_stack(self.stack_size))
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

    fn push_sized(&mut self, size: usize, value: ExprId) {
        self.set_stack(self.stack_size, value);
        self.stack_size += size;
    }

    pub fn push(&mut self, value: ExprId) {
        self.push_sized(1, value);
    }

    pub fn push2(&mut self, value: ExprId) {
        self.push_sized(2, value);
    }

    pub fn push_return_type(&mut self, return_type: &Option<TypeDescriptor<'code>>, value: ExprId) {
        if let Some(ret) = return_type {
            if is_type_descriptor_double_width(ret) {
                self.push2(value);
            } else {
                self.push(value);
            }
        } else {
            self.statements
                .push(Statement::Basic(BasicStatement::Calculate(value)));
        }
    }

    pub fn push_nat(&mut self, name_and_type: &NameAndType<'code>, value: ExprId) {
        if is_name_and_type_double_width(name_and_type) {
            self.push2(value);
        } else {
            self.push(value);
        }
    }

    pub fn cast_primitive(
        &mut self,
        from: PrimitiveType,
        to: PrimitiveType,
    ) -> Result<(), StackUnderflowError> {
        let value = self.pop_sized(from.size())?;
        self.push_sized(
            to.size(),
            self.arena
                .alloc(Expression::CastPrimitive { value, from, to }),
        );
        Ok(())
    }

    pub fn binop(
        &mut self,
        op: BinOp,
        res_ty: PrimitiveType,
        lhs_ty: PrimitiveType,
        rhs_ty: PrimitiveType,
    ) -> Result<(), StackUnderflowError> {
        let rhs = self.pop_sized(rhs_ty.size())?;
        let lhs = self.pop_sized(lhs_ty.size())?;
        self.push_sized(
            res_ty.size(),
            self.arena.alloc(Expression::BinOp { lhs, rhs, op }),
        );
        Ok(())
    }

    pub fn arith_binop(&mut self, op: BinOp, ty: PrimitiveType) -> Result<(), StackUnderflowError> {
        self.binop(op, ty, ty, ty)
    }

    fn get_var(&mut self, name: VariableName) -> ExprId {
        match self.active_defs.entry(name) {
            Entry::Occupied(entry) => self.arena.alloc(Expression::Variable {
                name,
                version: entry.get().version,
            }),
            Entry::Vacant(entry) => {
                let use_expr_id = self.arena.alloc_with(|use_expr_id| Expression::Variable {
                    name,
                    version: use_expr_id,
                });
                // Link future uses to the same version -- this reduces unresolved uses to one per
                // BB per variable.
                entry.insert(ActiveDef {
                    version: use_expr_id,
                    is_fake: true,
                });
                self.unresolved_uses
                    .entry(name)
                    .or_default()
                    .push((self.bb_id, use_expr_id));
                use_expr_id
            }
        }
    }

    // Takes `value` because we want to enforce that the value is computed before the assignment is
    // performed, i.e. that uses in `value` see old defs.
    fn set_var(&mut self, name: VariableName, value: ExprId) {
        let def_expr_id = self.arena.alloc_with(|def_expr_id| Expression::Variable {
            name,
            version: def_expr_id,
        });
        self.active_defs.insert(
            name,
            ActiveDef {
                version: def_expr_id,
                is_fake: false,
            },
        );
        self.statements
            .push(Statement::Basic(BasicStatement::Assign {
                target: def_expr_id,
                value,
            }));
    }

    pub fn get_stack(&mut self, position: usize) -> ExprId {
        self.get_var(VariableName {
            id: position,
            namespace: VariableNamespace::Stack,
        })
    }

    pub fn set_stack(&mut self, position: usize, value: ExprId) {
        self.set_var(
            VariableName {
                id: position,
                namespace: VariableNamespace::Stack,
            },
            value,
        );
    }

    pub fn get_slot(&mut self, id: usize) -> ExprId {
        self.get_var(VariableName {
            id,
            namespace: VariableNamespace::Slot,
        })
    }

    pub fn set_slot(&mut self, id: usize, value: ExprId) {
        self.set_var(
            VariableName {
                id,
                namespace: VariableNamespace::Slot,
            },
            value,
        );
    }

    pub fn get_tmp(&mut self, id: usize) -> ExprId {
        self.get_var(VariableName {
            id,
            namespace: VariableNamespace::Temporary,
        })
    }

    pub fn set_tmp(&mut self, id: usize, value: ExprId) {
        self.set_var(
            VariableName {
                id,
                namespace: VariableNamespace::Temporary,
            },
            value,
        );
    }

    pub fn copy(&mut self, target: usize, source: usize) {
        let value = self.get_stack(source);
        self.set_stack(target, value);
    }

    pub fn add(&mut self, stmt: Statement) {
        self.statements.push(stmt);
    }
}
