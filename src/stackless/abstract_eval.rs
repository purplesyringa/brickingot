use super::Statement;
use crate::arena::{Arena, ExprId};
use crate::ast::{
    BasicStatement, BinOp, Expression, PrimitiveType, Variable, VariableName, VariableNamespace,
};
use crate::preparse::insn_stack_effect::{
    is_name_and_type_double_width, is_type_descriptor_double_width,
};
use noak::{
    descriptor::{MethodDescriptor, TypeDescriptor},
    reader::cpool::value::NameAndType,
};
use rustc_hash::FxHashMap;
use thiserror::Error;

pub struct ActiveDef {
    // Can be `None` for stack variables until the BB is sealed.
    pub def_expr_id: Option<ExprId>,
    // The variable the definition sets. `var.name` can mismatch the name of the defined variable if
    // it's a `stackN = valueM` situation: `var.name` will be set to `valueM` to link preemptively.
    pub var: Variable,
    // `Some(stack_var)` indicates that the value is equal to `stack_var` at the end of the
    // predecessor, and that `var` is a value populated from `stack_var`. Only meaningful for
    // `stackN` definitions.
    pub copy_stack_from_predecessor: Option<Variable>,
}

pub struct UnresolvedUse {
    pub is_stack_manipulation: bool,
}

struct StackWrite {
    value_var: Variable,
    order_id: usize,
}

pub struct Machine<'arena, 'code> {
    pub arena: &'arena Arena<'code>,
    pub stack_size: usize,
    active_defs: FxHashMap<VariableName, ActiveDef>,
    stack_state: FxHashMap<usize, StackWrite>,
    pub unresolved_uses: FxHashMap<(usize, Variable), UnresolvedUse>,
    pub bb_id: usize,
    pub statements: Vec<Statement>,
    next_value_id: usize,
    next_order_id: usize,
}

#[derive(Debug, Error)]
#[error("Stack underflow")]
pub struct StackUnderflowError;

impl<'arena, 'code> Machine<'arena, 'code> {
    pub fn new(arena: &'arena Arena<'code>) -> Self {
        Self {
            arena,
            stack_size: 0,
            active_defs: FxHashMap::default(),
            stack_state: FxHashMap::default(),
            unresolved_uses: FxHashMap::default(),
            bb_id: usize::MAX,
            statements: Vec::new(),
            next_value_id: 0,
            next_order_id: 0,
        }
    }

    fn pop_sized(&mut self, size: usize) -> Result<ExprId, StackUnderflowError> {
        if self.stack_size < size {
            return Err(StackUnderflowError);
        }
        self.stack_size -= size;
        Ok(self.get_stack(self.stack_size, false))
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
        // Instructions that can work on types of both categories, like dup2, read the second stack
        // element for wide types. If we don't populate that element, these reads will either access
        // uninitialized memory, which triggers problems down the road, or access elements that have
        // already been popped, creating phantom uses. Using a filler value like `null` solves this.
        for offset in 1..size {
            self.set_stack(self.stack_size + offset, self.arena.alloc(Expression::Null));
        }
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
            self.add(Statement::Basic(BasicStatement::Calculate(value)));
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

    fn get_var(&mut self, name: VariableName, is_stack_manipulation: bool) -> ExprId {
        if let Some(def) = self.active_defs.get(&name) {
            if !is_stack_manipulation && let Some(var) = def.copy_stack_from_predecessor {
                self.unresolved_uses
                    .get_mut(&(self.bb_id, var))
                    .unwrap()
                    .is_stack_manipulation = false;
            }
            self.arena.alloc(Expression::Variable(def.var))
        } else {
            let use_expr_id = self.arena.alloc_with(|use_expr_id| {
                Expression::Variable(Variable {
                    name,
                    version: use_expr_id,
                })
            });
            self.unresolved_uses.insert(
                (
                    self.bb_id,
                    Variable {
                        name,
                        version: use_expr_id,
                    },
                ),
                UnresolvedUse {
                    is_stack_manipulation,
                },
            );
            use_expr_id
        }
    }

    // Takes `value` because we want to enforce that the value is computed before the assignment is
    // performed, i.e. that uses in `value` see old defs.
    fn set_var(&mut self, name: VariableName, value: ExprId) -> Variable {
        let def_expr_id = self.arena.alloc_with(|def_expr_id| {
            Expression::Variable(Variable {
                name,
                version: def_expr_id,
            })
        });
        let var = Variable {
            name,
            version: def_expr_id,
        };
        self.add(Statement::Basic(BasicStatement::Assign {
            target: def_expr_id,
            value,
        }));
        var
    }

    pub fn get_slot(&mut self, id: usize) -> ExprId {
        self.get_var(
            VariableName {
                id,
                namespace: VariableNamespace::Slot,
            },
            false,
        )
    }

    pub fn set_slot(&mut self, id: usize, value: ExprId) {
        let name = VariableName {
            id,
            namespace: VariableNamespace::Slot,
        };
        let var = self.set_var(name, value);
        self.active_defs.insert(
            name,
            ActiveDef {
                def_expr_id: Some(var.version),
                var,
                copy_stack_from_predecessor: None,
            },
        );
    }

    fn get_stack(&mut self, position: usize, is_stack_manipulation: bool) -> ExprId {
        self.get_var(
            VariableName {
                id: position,
                namespace: VariableNamespace::Stack,
            },
            is_stack_manipulation,
        )
    }

    fn set_stack(&mut self, position: usize, value: ExprId) {
        // Create an intermediate variable to link multiple uses of the expression together, even if
        // its stack location becomes overwritten. If `value` already refers to a value variable,
        // there's no need to create an intermediate one, as value variables cannot be overwritten
        // (except if re-entering the basic block).
        let value_var = if let Expression::Variable(value_var) = self.arena[value]
            && value_var.name.namespace == VariableNamespace::Value
        {
            value_var
        } else {
            self.next_value_id += 1;
            self.set_var(
                VariableName {
                    id: self.next_value_id - 1,
                    namespace: VariableNamespace::Value,
                },
                value,
            )
            // Value variables are never accessed by `get_var` or read by other BBs, so no need
            // to save their definitions. This significantly reduces the size of the hashmap.
        };

        let copy_stack_from_predecessor = if let Expression::Variable(var) = self.arena[value]
            && var.name.namespace == VariableNamespace::Stack
        {
            Some(var)
        } else {
            None
        };

        self.active_defs.insert(
            VariableName {
                id: position,
                namespace: VariableNamespace::Stack,
            },
            ActiveDef {
                def_expr_id: None,
                var: value_var,
                copy_stack_from_predecessor,
            },
        );

        // Emitting assignment to stack variables is delayed until the end of the basic block, so
        // that definitions that are soon overwritten aren't present in the IR.
        self.stack_state.insert(
            position,
            StackWrite {
                value_var,
                order_id: self.next_order_id,
            },
        );
        self.next_order_id += 1;
    }

    pub fn flush_stack_writes(&mut self) {
        // Emit delayed stack assignments. Make sure not to reorder them, as reordering
        //     stack1 = stack0
        //     stack0 = value0
        // is wrong even if `stack0`s have different versions.
        let mut delayed_stack_assignments: Vec<(usize, StackWrite)> =
            self.stack_state.drain().collect();
        delayed_stack_assignments.sort_by_key(|(_, write)| write.order_id);

        for (position, write) in delayed_stack_assignments {
            let name = VariableName {
                namespace: VariableNamespace::Stack,
                id: position,
            };
            let def_expr_id = self.arena.alloc_with(|def_expr_id| {
                Expression::Variable(Variable {
                    name,
                    version: def_expr_id,
                })
            });
            self.active_defs.get_mut(&name).unwrap().def_expr_id = Some(def_expr_id);
            self.statements
                .push(Statement::Basic(BasicStatement::Assign {
                    target: def_expr_id,
                    value: self.arena.alloc(Expression::Variable(write.value_var)),
                }));
        }
    }

    // Drop writes if no one can possibly see them. This is useful because it removes all writes to
    // stack variables from functions with linear control flow.
    pub fn drop_stack_writes(&mut self) {
        self.stack_state.clear();
    }

    pub fn seal_basic_block(&mut self) -> FxHashMap<VariableName, ActiveDef> {
        self.flush_stack_writes();
        core::mem::take(&mut self.active_defs)
    }

    pub fn copy(&mut self, target: usize, source: usize) {
        let value = self.get_stack(source, true);
        self.set_stack(target, value);
    }

    pub fn add(&mut self, stmt: Statement) {
        self.statements.push(stmt);
    }
}
