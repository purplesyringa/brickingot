use super::Statement;
use crate::ast::{
    Arena, BasicStatement, BinOp, ExprId, Expression, PrimitiveType, Variable, VariableName,
    VariableNamespace, Version,
};
use crate::class::MethodDescriptorInfo;
use crate::preparse::insn_stack_effect::{nat_width, type_descriptor_width};
use crate::var;
use noak::{descriptor::TypeDescriptor, reader::cpool::value::NameAndType};
use rustc_hash::FxHashMap;
use thiserror::Error;

pub struct ActiveDef {
    // Can be `None` for stack variables until the BB is sealed.
    pub def_version: Option<Version>,
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

#[derive(Default)]
pub struct SealedBlock {
    pub statements: Vec<Statement>,
    pub active_defs_at_end: FxHashMap<VariableName, ActiveDef>,
    pub slot_defs: FxHashMap<VariableName, Vec<Version>>,
}

pub struct Machine<'arena, 'code> {
    pub arena: &'arena Arena<'code>,
    pub stack_size: usize,
    active_defs: FxHashMap<VariableName, ActiveDef>,
    slot_defs: FxHashMap<VariableName, Vec<Version>>, // versions correspond to the LHS expr
    stack_state: FxHashMap<usize, StackWrite>,
    pub unresolved_uses: FxHashMap<(usize, Variable), UnresolvedUse>,
    pub bb_id: usize,
    pub statements: Vec<Statement>,
    next_value_id: usize,
    next_order_id: usize,
    pub address_to_bb_id: FxHashMap<u32, usize>,
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
            slot_defs: FxHashMap::default(),
            stack_state: FxHashMap::default(),
            unresolved_uses: FxHashMap::default(),
            bb_id: usize::MAX,
            statements: Vec::new(),
            next_value_id: 0,
            next_order_id: 0,
            address_to_bb_id: FxHashMap::default(),
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
        method_info: &MethodDescriptorInfo<'code>,
    ) -> Result<Vec<ExprId>, StackUnderflowError> {
        let sizes = &method_info.parameter_sizes;
        let mut arguments = vec![ExprId(0); sizes.len()];
        for (i, size) in sizes.iter().enumerate().rev() {
            arguments[i] = self.pop_sized(size)?;
        }
        Ok(arguments)
    }

    pub fn pop_nat(
        &mut self,
        name_and_type: &NameAndType<'code>,
    ) -> Result<ExprId, StackUnderflowError> {
        self.pop_sized(nat_width(name_and_type))
    }

    fn push_sized(&mut self, size: usize, value: ExprId) {
        self.set_stack(self.stack_size, value);
        // Instructions that can work on types of both categories, like dup2, read the second stack
        // element for wide types. If we don't populate that element, these reads will either access
        // uninitialized memory, which triggers problems down the road, or access elements that have
        // already been popped, creating phantom uses. Using a filler value like `null` solves this.
        for offset in 1..size {
            self.set_stack(self.stack_size + offset, self.arena.null());
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
            self.push_sized(type_descriptor_width(ret.clone()), value);
        } else {
            self.add(Statement::Basic(BasicStatement::Calculate(value)));
        }
    }

    pub fn push_nat(&mut self, name_and_type: &NameAndType<'code>, value: ExprId) {
        self.push_sized(nat_width(name_and_type), value)
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
            self.arena.var(def.var)
        } else {
            let (var, use_expr_id) = self.arena.var_name(name);
            self.unresolved_uses.insert(
                (self.bb_id, var),
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
        let (var, def_expr_id) = self.arena.var_name(name);
        self.add(Statement::Basic(BasicStatement::Assign {
            target: def_expr_id,
            value,
        }));
        var
    }

    pub fn get_slot(&mut self, id: usize) -> ExprId {
        self.get_var(var!(slot id), false)
    }

    pub fn set_slot(&mut self, id: usize, value: ExprId) {
        let var = self.set_var(var!(slot id), value);
        self.active_defs.insert(
            var.name,
            ActiveDef {
                def_version: Some(var.version),
                var,
                copy_stack_from_predecessor: None,
            },
        );
        self.slot_defs
            .entry(var.name)
            .or_default()
            .push(var.version);
    }

    fn get_stack(&mut self, position: usize, is_stack_manipulation: bool) -> ExprId {
        self.get_var(var!(stack position), is_stack_manipulation)
    }

    fn set_stack(&mut self, position: usize, value: ExprId) {
        // Create an intermediate variable to link multiple uses of the expression together, even if
        // its stack location becomes overwritten. If `value` already refers to a value variable,
        // there's no need to create an intermediate one, as value variables cannot be overwritten
        // (except by re-entering the basic block).
        let value_var = if let Expression::Variable(value_var) = self.arena[value]
            && value_var.name.namespace == VariableNamespace::Value
        {
            value_var
        } else {
            let id = self.next_value_id;
            self.next_value_id += 1;
            self.set_var(var!(value id), value)
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
            var!(stack position),
            ActiveDef {
                def_version: None,
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
            let (var, def_expr_id) = self.arena.var_name(var!(stack position));
            self.active_defs.get_mut(&var.name).unwrap().def_version = Some(var.version);
            self.statements
                .push(Statement::Basic(BasicStatement::Assign {
                    target: def_expr_id,
                    value: self.arena.var(write.value_var),
                }));
        }
    }

    // Drop writes if no one can possibly see them. This is useful because it removes all writes to
    // stack variables from functions with linear control flow.
    pub fn drop_stack_writes(&mut self) {
        self.stack_state.clear();
    }

    pub fn seal_basic_block(&mut self) -> SealedBlock {
        self.flush_stack_writes();
        SealedBlock {
            statements: core::mem::take(&mut self.statements),
            active_defs_at_end: core::mem::take(&mut self.active_defs),
            slot_defs: core::mem::take(&mut self.slot_defs),
        }
    }

    pub fn copy(&mut self, target: usize, source: usize) {
        let value = self.get_stack(source, true);
        self.set_stack(target, value);
    }

    pub fn add(&mut self, stmt: Statement) {
        self.statements.push(stmt);
    }
}
