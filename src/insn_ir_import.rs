use crate::ast::{
    ArenaRef, BasicStatement, BinOp, BoxedExpr, Call, CallKind, Expression, Field, PrimitiveType,
    Str, Type, UnaryOp,
};
use crate::stack_machine::{StackMachine, StackUnderflowError};
use crate::stackless::{Statement, Switch};
use noak::{
    descriptor::MethodDescriptor,
    error::DecodeError,
    reader::{
        attributes::{
            ArrayType,
            RawInstruction::{self, *},
        },
        cpool::{
            self, value::FieldRef, ConstantPool, Dynamic, Index, InterfaceMethodRef, Item,
            MethodHandle, MethodRef,
        },
    },
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum InsnIrImportError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("Accessed more elements than there are in the stack")]
    StackUnderflow(#[from] StackUnderflowError),

    #[error("ldc instruction accessed a constant of an invalid type")]
    InvalidLdc,

    #[error("ldc2 instruction accessed a constant of an invalid type")]
    InvalidLdc2,
}

#[must_use = "returns a statement that needs to be emitted manually"]
fn assign<'arena, 'code>(
    target: BoxedExpr<'arena, 'code>,
    value: BoxedExpr<'arena, 'code>,
) -> Statement<'arena, 'code> {
    Statement::Basic(BasicStatement::Assign { target, value })
}

fn field<'arena, 'code>(
    arena: ArenaRef<'arena, 'code>,
    object: Option<BoxedExpr<'arena, 'code>>,
    field: &FieldRef<'code>,
) -> BoxedExpr<'arena, 'code> {
    arena.alloc(Expression::Field(Field {
        object,
        class: Str(field.class.name),
        name: Str(field.name_and_type.name),
        descriptor: Str(field.name_and_type.descriptor),
    }))
}

fn invoke<'arena, 'code>(
    pool: &ConstantPool<'code>,
    stack: &mut StackMachine<'arena, 'code>,
    index: Index<Item<'code>>,
    has_receiver: bool,
    is_special: bool,
) -> Result<Statement<'arena, 'code>, InsnIrImportError> {
    let (class, name_and_type) = match pool.get(index)? {
        Item::MethodRef(MethodRef {
            class,
            name_and_type,
        }) => (class, name_and_type),
        Item::InterfaceMethodRef(InterfaceMethodRef {
            class,
            name_and_type,
        }) => (class, name_and_type),
        _ => unreachable!("pre-parsing should have checked the types"),
    };

    let name_and_type = pool.retrieve(*name_and_type)?;
    let class_or_interface = Str(pool.retrieve(*class)?.name);
    let method_descriptor = MethodDescriptor::parse(name_and_type.descriptor)?;
    let arguments = stack.pop_method_arguments(&method_descriptor)?;

    let kind = if has_receiver {
        CallKind::Method {
            class_or_interface,
            object: stack.pop()?,
            is_special,
        }
    } else {
        CallKind::Static { class_or_interface }
    };

    Ok(stack.push_return_type(
        &method_descriptor.return_type(),
        stack.arena.alloc(Expression::Call(Call {
            method_name: Str(name_and_type.name),
            kind,
            arguments,
            descriptor: Str(name_and_type.descriptor),
        })),
    ))
}

pub fn import_insn_to_ir<'arena, 'code>(
    stack: &mut StackMachine<'arena, 'code>,
    pool: &ConstantPool<'code>,
    address: u32,
    insn: &RawInstruction<'code>,
    stmts: &mut Vec<Statement<'arena, 'code>>,
) -> Result<(), InsnIrImportError> {
    let arena = stack.arena;

    let offset_to_address = |offset: i32| -> u32 { (address as i32 + offset) as u32 };

    let jump = |condition: BoxedExpr<'arena, 'code>, offset: i32| -> Statement<'arena, 'code> {
        Statement::Jump {
            condition,
            // The preparsing steps ensures all goto destinations are valid instruction addresses.
            // This will be replaced by the instruction index on a later pass, after all
            // instructions are emitted.
            target: offset_to_address(offset) as usize,
        }
    };

    match insn {
        // Array loads/stores
        AALoad | BALoad | CALoad | FALoad | IALoad | SALoad => {
            let index = stack.pop()?;
            let array = stack.pop()?;
            stmts.push(stack.push(arena.alloc(Expression::ArrayElement { array, index })));
        }
        DALoad | LALoad => {
            let index = stack.pop()?;
            let array = stack.pop()?;
            stmts.push(stack.push2(arena.alloc(Expression::ArrayElement { array, index })));
        }
        AAStore | BAStore | CAStore | FAStore | IAStore | SAStore => {
            let value = stack.pop()?;
            let index = stack.pop()?;
            let array = stack.pop()?;
            stmts.push(assign(
                arena.alloc(Expression::ArrayElement { array, index }),
                value,
            ));
        }
        DAStore | LAStore => {
            let value = stack.pop2()?;
            let index = stack.pop()?;
            let array = stack.pop()?;
            stmts.push(assign(
                arena.alloc(Expression::ArrayElement { array, index }),
                value,
            ));
        }

        // Slot load/stores
        ALoad { index } | FLoad { index } | ILoad { index } => {
            stmts.push(stack.push(arena.slot(*index as usize)))
        }
        ALoadW { index } | FLoadW { index } | ILoadW { index } => {
            stmts.push(stack.push(arena.slot(*index as usize)))
        }
        DLoad { index } | LLoad { index } => stmts.push(stack.push2(arena.slot(*index as usize))),
        DLoadW { index } | LLoadW { index } => stmts.push(stack.push2(arena.slot(*index as usize))),
        ALoad0 | FLoad0 | ILoad0 => stmts.push(stack.push(arena.slot(0))),
        ALoad1 | FLoad1 | ILoad1 => stmts.push(stack.push(arena.slot(1))),
        ALoad2 | FLoad2 | ILoad2 => stmts.push(stack.push(arena.slot(2))),
        ALoad3 | FLoad3 | ILoad3 => stmts.push(stack.push(arena.slot(3))),
        DLoad0 | LLoad0 => stmts.push(stack.push2(arena.slot(0))),
        DLoad1 | LLoad1 => stmts.push(stack.push2(arena.slot(1))),
        DLoad2 | LLoad2 => stmts.push(stack.push2(arena.slot(2))),
        DLoad3 | LLoad3 => stmts.push(stack.push2(arena.slot(3))),

        AStore { index } | FStore { index } | IStore { index } => {
            stmts.push(assign(arena.slot(*index as usize), stack.pop()?));
        }
        AStoreW { index } | FStoreW { index } | IStoreW { index } => {
            stmts.push(assign(arena.slot(*index as usize), stack.pop()?));
        }
        DStore { index } | LStore { index } => {
            stmts.push(assign(arena.slot(*index as usize), stack.pop2()?));
        }
        DStoreW { index } | LStoreW { index } => {
            stmts.push(assign(arena.slot(*index as usize), stack.pop2()?));
        }
        AStore0 | FStore0 | IStore0 => stmts.push(assign(arena.slot(0), stack.pop()?)),
        AStore1 | FStore1 | IStore1 => stmts.push(assign(arena.slot(1), stack.pop()?)),
        AStore2 | FStore2 | IStore2 => stmts.push(assign(arena.slot(2), stack.pop()?)),
        AStore3 | FStore3 | IStore3 => stmts.push(assign(arena.slot(3), stack.pop()?)),
        DStore0 | LStore0 => stmts.push(assign(arena.slot(0), stack.pop2()?)),
        DStore1 | LStore1 => stmts.push(assign(arena.slot(1), stack.pop2()?)),
        DStore2 | LStore2 => stmts.push(assign(arena.slot(2), stack.pop2()?)),
        DStore3 | LStore3 => stmts.push(assign(arena.slot(3), stack.pop2()?)),

        // Constants
        AConstNull => stmts.push(stack.push(arena.null())),
        BIPush { value } => stmts.push(stack.push(arena.alloc(Expression::ConstByte(*value)))),
        SIPush { value } => stmts.push(stack.push(arena.alloc(Expression::ConstShort(*value)))),
        FConst0 => stmts.push(stack.push(arena.alloc(Expression::ConstFloat(0.0)))),
        FConst1 => stmts.push(stack.push(arena.alloc(Expression::ConstFloat(1.0)))),
        FConst2 => stmts.push(stack.push(arena.alloc(Expression::ConstFloat(2.0)))),
        IConstM1 => stmts.push(stack.push(arena.alloc(Expression::ConstInt(-1)))),
        IConst0 => stmts.push(stack.push(arena.alloc(Expression::ConstInt(0)))),
        IConst1 => stmts.push(stack.push(arena.alloc(Expression::ConstInt(1)))),
        IConst2 => stmts.push(stack.push(arena.alloc(Expression::ConstInt(2)))),
        IConst3 => stmts.push(stack.push(arena.alloc(Expression::ConstInt(3)))),
        IConst4 => stmts.push(stack.push(arena.alloc(Expression::ConstInt(4)))),
        IConst5 => stmts.push(stack.push(arena.alloc(Expression::ConstInt(5)))),
        DConst0 => stmts.push(stack.push2(arena.alloc(Expression::ConstDouble(0.0)))),
        DConst1 => stmts.push(stack.push2(arena.alloc(Expression::ConstDouble(1.0)))),
        LConst0 => stmts.push(stack.push2(arena.alloc(Expression::ConstLong(0)))),
        LConst1 => stmts.push(stack.push2(arena.alloc(Expression::ConstLong(1)))),
        LdC { index } | LdCW { index } => match pool.get(*index)? {
            Item::Integer(cpool::Integer { value }) => {
                stmts.push(stack.push(arena.alloc(Expression::ConstInt(*value))))
            }
            Item::Float(cpool::Float { value }) => {
                stmts.push(stack.push(arena.alloc(Expression::ConstFloat(*value))))
            }
            Item::Class(cpool::Class { name }) => {
                stmts.push(stack.push(arena.alloc(Expression::Class(Str(pool.retrieve(*name)?)))))
            }
            Item::String(cpool::String { string }) => stmts
                .push(stack.push(arena.alloc(Expression::ConstString(pool.retrieve(*string)?)))),
            Item::MethodHandle(_) => {
                stmts.push(stack.push(arena.alloc(Expression::ConstMethodHandle(
                    pool.retrieve(Index::<MethodHandle>::new(index.as_u16()).unwrap())?,
                ))))
            }
            Item::MethodType(cpool::MethodType { descriptor }) => {
                stmts.push(stack.push(arena.alloc(Expression::ConstMethodType {
                    descriptor: pool.retrieve(*descriptor)?,
                })))
            }
            Item::Dynamic(_) => stmts.push(stack.push(arena.alloc(Expression::DynamicConst(
                pool.retrieve(Index::<Dynamic>::new(index.as_u16()).unwrap())?,
            )))),
            _ => return Err(InsnIrImportError::InvalidLdc),
        },
        LdC2W { index } => match pool.get(*index)? {
            Item::Long(cpool::Long { value }) => {
                stmts.push(stack.push2(arena.alloc(Expression::ConstLong(*value))))
            }
            Item::Double(cpool::Double { value }) => {
                stmts.push(stack.push2(arena.alloc(Expression::ConstDouble(*value))))
            }
            _ => return Err(InsnIrImportError::InvalidLdc2),
        },

        // Conversions
        CheckCast { index } => {
            let value = stack.pop()?;
            stmts.push(stack.push(arena.alloc(Expression::CastReference {
                value,
                class: Str(pool.retrieve(*index)?.name),
            })));
        }
        D2F => stmts.push(stack.cast_primitive(PrimitiveType::Double, PrimitiveType::Float)?),
        D2I => stmts.push(stack.cast_primitive(PrimitiveType::Double, PrimitiveType::Int)?),
        D2L => stmts.push(stack.cast_primitive(PrimitiveType::Double, PrimitiveType::Long)?),
        F2D => stmts.push(stack.cast_primitive(PrimitiveType::Float, PrimitiveType::Double)?),
        F2I => stmts.push(stack.cast_primitive(PrimitiveType::Float, PrimitiveType::Int)?),
        F2L => stmts.push(stack.cast_primitive(PrimitiveType::Float, PrimitiveType::Long)?),
        I2B => stmts.push(stack.cast_primitive(PrimitiveType::Int, PrimitiveType::Byte)?),
        I2C => stmts.push(stack.cast_primitive(PrimitiveType::Int, PrimitiveType::Char)?),
        I2D => stmts.push(stack.cast_primitive(PrimitiveType::Int, PrimitiveType::Double)?),
        I2F => stmts.push(stack.cast_primitive(PrimitiveType::Int, PrimitiveType::Float)?),
        I2L => stmts.push(stack.cast_primitive(PrimitiveType::Int, PrimitiveType::Long)?),
        I2S => stmts.push(stack.cast_primitive(PrimitiveType::Int, PrimitiveType::Short)?),
        L2D => stmts.push(stack.cast_primitive(PrimitiveType::Long, PrimitiveType::Double)?),
        L2F => stmts.push(stack.cast_primitive(PrimitiveType::Long, PrimitiveType::Float)?),
        L2I => stmts.push(stack.cast_primitive(PrimitiveType::Long, PrimitiveType::Int)?),

        // Arithmetic
        DAdd => stmts.push(stack.arith_binop(BinOp::Add, PrimitiveType::Double)?),
        DSub => stmts.push(stack.arith_binop(BinOp::Sub, PrimitiveType::Double)?),
        DMul => stmts.push(stack.arith_binop(BinOp::Mul, PrimitiveType::Double)?),
        DDiv => stmts.push(stack.arith_binop(BinOp::Div { is_fp: true }, PrimitiveType::Double)?),
        DRem => stmts.push(stack.arith_binop(BinOp::Rem { is_fp: true }, PrimitiveType::Double)?),
        FAdd => stmts.push(stack.arith_binop(BinOp::Add, PrimitiveType::Float)?),
        FSub => stmts.push(stack.arith_binop(BinOp::Sub, PrimitiveType::Float)?),
        FMul => stmts.push(stack.arith_binop(BinOp::Mul, PrimitiveType::Float)?),
        FDiv => stmts.push(stack.arith_binop(BinOp::Div { is_fp: true }, PrimitiveType::Float)?),
        FRem => stmts.push(stack.arith_binop(BinOp::Rem { is_fp: true }, PrimitiveType::Float)?),
        IAdd => stmts.push(stack.arith_binop(BinOp::Add, PrimitiveType::Int)?),
        ISub => stmts.push(stack.arith_binop(BinOp::Sub, PrimitiveType::Int)?),
        IMul => stmts.push(stack.arith_binop(BinOp::Mul, PrimitiveType::Int)?),
        IDiv => stmts.push(stack.arith_binop(BinOp::Div { is_fp: false }, PrimitiveType::Int)?),
        IRem => stmts.push(stack.arith_binop(BinOp::Rem { is_fp: false }, PrimitiveType::Int)?),
        LAdd => stmts.push(stack.arith_binop(BinOp::Add, PrimitiveType::Long)?),
        LSub => stmts.push(stack.arith_binop(BinOp::Sub, PrimitiveType::Long)?),
        LMul => stmts.push(stack.arith_binop(BinOp::Mul, PrimitiveType::Long)?),
        LDiv => stmts.push(stack.arith_binop(BinOp::Div { is_fp: false }, PrimitiveType::Long)?),
        LRem => stmts.push(stack.arith_binop(BinOp::Rem { is_fp: false }, PrimitiveType::Long)?),
        IAnd => stmts.push(stack.arith_binop(BinOp::And, PrimitiveType::Int)?),
        IOr => stmts.push(stack.arith_binop(BinOp::Or, PrimitiveType::Int)?),
        IXor => stmts.push(stack.arith_binop(BinOp::Xor, PrimitiveType::Int)?),
        LAnd => stmts.push(stack.arith_binop(BinOp::And, PrimitiveType::Long)?),
        LOr => stmts.push(stack.arith_binop(BinOp::Or, PrimitiveType::Long)?),
        LXor => stmts.push(stack.arith_binop(BinOp::Xor, PrimitiveType::Long)?),
        IShL => stmts.push(stack.arith_binop(BinOp::Shl, PrimitiveType::Int)?),
        IShR => stmts.push(stack.arith_binop(BinOp::Shr, PrimitiveType::Int)?),
        IUShR => stmts.push(stack.arith_binop(BinOp::UnsignedShr, PrimitiveType::Int)?),
        LShL => stmts.push(stack.binop(
            BinOp::Shl,
            PrimitiveType::Long,
            PrimitiveType::Long,
            PrimitiveType::Int,
        )?),
        LShR => stmts.push(stack.binop(
            BinOp::Shr,
            PrimitiveType::Long,
            PrimitiveType::Long,
            PrimitiveType::Int,
        )?),
        LUShR => stmts.push(stack.binop(
            BinOp::UnsignedShr,
            PrimitiveType::Long,
            PrimitiveType::Long,
            PrimitiveType::Int,
        )?),
        DCmpG => stmts.push(stack.binop(
            BinOp::Compare {
                fp_negative_on_nan: false,
            },
            PrimitiveType::Int,
            PrimitiveType::Double,
            PrimitiveType::Double,
        )?),
        DCmpL => stmts.push(stack.binop(
            BinOp::Compare {
                fp_negative_on_nan: true,
            },
            PrimitiveType::Int,
            PrimitiveType::Double,
            PrimitiveType::Double,
        )?),
        FCmpG => stmts.push(stack.binop(
            BinOp::Compare {
                fp_negative_on_nan: false,
            },
            PrimitiveType::Int,
            PrimitiveType::Float,
            PrimitiveType::Float,
        )?),
        FCmpL => stmts.push(stack.binop(
            BinOp::Compare {
                fp_negative_on_nan: true,
            },
            PrimitiveType::Int,
            PrimitiveType::Float,
            PrimitiveType::Float,
        )?),
        LCmp => stmts.push(stack.binop(
            BinOp::Compare {
                fp_negative_on_nan: false,
            },
            PrimitiveType::Int,
            PrimitiveType::Long,
            PrimitiveType::Long,
        )?),
        DNeg | LNeg => {
            let argument = stack.pop2()?;
            stmts.push(stack.push2(arena.alloc(Expression::UnaryOp {
                argument,
                op: UnaryOp::Neg,
            })));
        }
        FNeg | INeg => {
            let argument = stack.pop()?;
            stmts.push(stack.push(arena.alloc(Expression::UnaryOp {
                argument,
                op: UnaryOp::Neg,
            })));
        }

        // Stack manipulation
        Dup => {
            if stack.stack_size < 1 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            stmts.push(stack.copy(stack.stack_size, stack.stack_size - 1));
            stack.stack_size += 1;
        }
        DupX1 => {
            if stack.stack_size < 2 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            // Can't just clone Expression because variables will get reassigned and we don't have
            // SSA yet, need to perform something similar to a temporary-variable swap instead.
            stmts.extend([
                stack.copy(stack.stack_size, stack.stack_size - 1),
                stack.copy(stack.stack_size - 1, stack.stack_size - 2),
                stack.copy(stack.stack_size - 2, stack.stack_size),
            ]);
            stack.stack_size += 1;
        }
        DupX2 => {
            if stack.stack_size < 3 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            stmts.extend([
                stack.copy(stack.stack_size, stack.stack_size - 1),
                stack.copy(stack.stack_size - 1, stack.stack_size - 2),
                stack.copy(stack.stack_size - 2, stack.stack_size - 3),
                stack.copy(stack.stack_size - 3, stack.stack_size),
            ]);
            stack.stack_size += 1;
        }
        Dup2 => {
            if stack.stack_size < 2 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            stmts.push(stack.copy(stack.stack_size, stack.stack_size - 2));
            stack.stack_size += 2;
        }
        Dup2X1 => {
            if stack.stack_size < 3 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            stmts.extend([
                stack.copy(stack.stack_size + 1, stack.stack_size - 1),
                stack.copy(stack.stack_size, stack.stack_size - 2),
                stack.copy(stack.stack_size - 1, stack.stack_size - 3),
                stack.copy(stack.stack_size - 2, stack.stack_size + 1),
                stack.copy(stack.stack_size - 3, stack.stack_size),
            ]);
            stack.stack_size += 2;
        }
        Dup2X2 => {
            if stack.stack_size < 4 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            stmts.extend([
                stack.copy(stack.stack_size + 1, stack.stack_size - 1),
                stack.copy(stack.stack_size, stack.stack_size - 2),
                stack.copy(stack.stack_size - 1, stack.stack_size - 3),
                stack.copy(stack.stack_size - 2, stack.stack_size - 4),
                stack.copy(stack.stack_size - 3, stack.stack_size + 1),
                stack.copy(stack.stack_size - 4, stack.stack_size),
            ]);
            stack.stack_size += 2;
        }
        Pop => {
            stack.pop()?;
        }
        Pop2 => {
            stack.pop2()?;
        }
        Swap => {
            // Can't just pop and push twice because variables will get reassigned and we don't have
            // SSA yet, need to introduce a temporary variable.
            if stack.stack_size < 2 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            stmts.extend([
                assign(arena.tmp(0), stack.at(stack.stack_size - 1)),
                stack.copy(stack.stack_size - 1, stack.stack_size - 2),
                stack.assign(stack.stack_size - 2, arena.tmp(0)),
            ]);
        }

        // Exits
        AThrow => stmts.push(Statement::Basic(BasicStatement::Throw {
            exception: stack.pop()?,
        })),
        AReturn | FReturn | IReturn => stmts.push(Statement::Basic(BasicStatement::Return {
            value: stack.pop()?,
        })),
        DReturn | LReturn => stmts.push(Statement::Basic(BasicStatement::Return {
            value: stack.pop2()?,
        })),
        Return => stmts.push(Statement::Basic(BasicStatement::ReturnVoid)),

        // Jumps
        Goto { offset } => stmts.push(jump(arena.int(1), *offset as i32)),
        GotoW { offset } => stmts.push(jump(arena.int(1), *offset)),
        IfACmpEq { offset } => {
            let rhs = stack.pop()?;
            let lhs = stack.pop()?;
            stmts.push(jump(
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Eq,
                }),
                *offset as i32,
            ));
        }
        IfACmpNe { offset } => {
            let rhs = stack.pop()?;
            let lhs = stack.pop()?;
            stmts.push(jump(
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Ne,
                }),
                *offset as i32,
            ));
        }
        IfICmpEq { offset } => {
            let rhs = stack.pop()?;
            let lhs = stack.pop()?;
            stmts.push(jump(
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Eq,
                }),
                *offset as i32,
            ));
        }
        IfICmpNe { offset } => {
            let rhs = stack.pop()?;
            let lhs = stack.pop()?;
            stmts.push(jump(
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Ne,
                }),
                *offset as i32,
            ));
        }
        IfICmpLt { offset } => {
            let rhs = stack.pop()?;
            let lhs = stack.pop()?;
            stmts.push(jump(
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Lt,
                }),
                *offset as i32,
            ));
        }
        IfICmpGe { offset } => {
            let rhs = stack.pop()?;
            let lhs = stack.pop()?;
            stmts.push(jump(
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Ge,
                }),
                *offset as i32,
            ));
        }
        IfICmpGt { offset } => {
            let rhs = stack.pop()?;
            let lhs = stack.pop()?;
            stmts.push(jump(
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Gt,
                }),
                *offset as i32,
            ));
        }
        IfICmpLe { offset } => {
            let rhs = stack.pop()?;
            let lhs = stack.pop()?;
            stmts.push(jump(
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Le,
                }),
                *offset as i32,
            ));
        }
        IfEq { offset } => stmts.push(jump(
            arena.alloc(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: arena.int(0),
                op: BinOp::Eq,
            }),
            *offset as i32,
        )),
        IfNe { offset } => stmts.push(jump(
            arena.alloc(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: arena.int(0),
                op: BinOp::Ne,
            }),
            *offset as i32,
        )),
        IfLt { offset } => stmts.push(jump(
            arena.alloc(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: arena.int(0),
                op: BinOp::Lt,
            }),
            *offset as i32,
        )),
        IfGe { offset } => stmts.push(jump(
            arena.alloc(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: arena.int(0),
                op: BinOp::Ge,
            }),
            *offset as i32,
        )),
        IfGt { offset } => stmts.push(jump(
            arena.alloc(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: arena.int(0),
                op: BinOp::Gt,
            }),
            *offset as i32,
        )),
        IfLe { offset } => stmts.push(jump(
            arena.alloc(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: arena.int(0),
                op: BinOp::Le,
            }),
            *offset as i32,
        )),
        IfNonNull { offset } => stmts.push(jump(
            arena.alloc(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: arena.null(),
                op: BinOp::Ne,
            }),
            *offset as i32,
        )),
        IfNull { offset } => stmts.push(jump(
            arena.alloc(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: arena.null(),
                op: BinOp::Eq,
            }),
            *offset as i32,
        )),
        LookupSwitch(switch) => stmts.push(Statement::Switch(Switch {
            key: stack.pop()?,
            arms: switch
                .pairs()
                .map(|pair| (pair.key(), offset_to_address(pair.offset()) as usize))
                .collect(),
            default: offset_to_address(switch.default_offset()) as usize,
        })),
        TableSwitch(switch) => stmts.push(Statement::Switch(Switch {
            key: stack.pop()?,
            arms: switch
                .pairs()
                .map(|pair| (pair.key(), offset_to_address(pair.offset()) as usize))
                .collect(),
            default: offset_to_address(switch.default_offset()) as usize,
        })),

        // Function calls
        InvokeDynamic { index } => {
            let indy = pool.retrieve(*index)?;
            let method_descriptor = MethodDescriptor::parse(indy.name_and_type.descriptor)?;
            let arguments = stack.pop_method_arguments(&method_descriptor)?;
            stmts.push(stack.push_return_type(
                &method_descriptor.return_type(),
                arena.alloc(Expression::Call(Call {
                    method_name: Str(indy.name_and_type.name),
                    kind: CallKind::Dynamic {
                        bootstrap_method_attr: indy.bootstrap_method_attr,
                    },
                    arguments,
                    descriptor: Str(indy.name_and_type.descriptor),
                })),
            ));
        }
        InvokeSpecial { index } => {
            // There simply isn't a good way to handle special invokes here yet. They can either
            // indicate super calls or normal calls (usually to `private` methods, when
            // `invokespecial` is basically treated as `invokenonvirtual`) depending on whether the
            // type of `this` matches the type in the descriptor, but we don't *know* the type of
            // `this` until SSA, so we can't obtain that information until then. Similarly, we don't
            // know if an `<init>` invocation initializes a newly created object (via `new`) or is
            // a call to a super constructor (via `super(...)`), so we can't even perform that
            // rewrite.
            stmts.push(invoke(
                pool,
                stack,
                Index::new(index.as_u16()).unwrap(),
                true,
                true,
            )?);
        }
        InvokeStatic { index } => stmts.push(invoke(pool, stack, *index, false, false)?),
        InvokeInterface { index, .. } => stmts.push(invoke(
            pool,
            stack,
            Index::new(index.as_u16()).unwrap(),
            true,
            false,
        )?),
        InvokeVirtual { index } => stmts.push(invoke(
            pool,
            stack,
            Index::new(index.as_u16()).unwrap(),
            true,
            false,
        )?),

        // Field operations
        GetField { index } => {
            let field_ref = pool.retrieve(*index)?;
            let object = stack.pop()?;
            stmts.push(stack.push_nat(
                &field_ref.name_and_type,
                field(arena, Some(object), &field_ref),
            ));
        }
        GetStatic { index } => {
            let field_ref = pool.retrieve(*index)?;
            stmts.push(stack.push_nat(&field_ref.name_and_type, field(arena, None, &field_ref)));
        }
        PutField { index } => {
            let field_ref = pool.retrieve(*index)?;
            let value = stack.pop_nat(&field_ref.name_and_type)?;
            let object = stack.pop()?;
            stmts.push(assign(field(arena, Some(object), &field_ref), value));
        }
        PutStatic { index } => {
            let field_ref = pool.retrieve(*index)?;
            let value = stack.pop_nat(&field_ref.name_and_type)?;
            stmts.push(assign(field(arena, None, &field_ref), value));
        }

        // Miscellaneous
        ANewArray { index } => {
            let length = stack.pop()?;
            stmts.push(stack.push(arena.alloc(Expression::NewArray {
                element_type: Type::Reference(Str(pool.retrieve(*index)?.name)),
                lengths: vec![length],
            })));
        }
        ArrayLength => {
            let array = stack.pop()?;
            stmts.push(stack.push(arena.alloc(Expression::ArrayLength { array })));
        }
        MultiANewArray { index, dimensions } => {
            let mut lengths: Vec<BoxedExpr<'arena, 'code>> = (0..*dimensions)
                .map(|_| stack.pop())
                .collect::<Result<_, _>>()?;
            lengths.reverse();
            stmts.push(stack.push(arena.alloc(Expression::NewArray {
                element_type: Type::Reference(Str(pool.retrieve(*index)?.name)),
                lengths,
            })));
        }
        IInc { index, value } => {
            stmts.push(assign(
                arena.slot(*index as usize),
                arena.alloc(Expression::BinOp {
                    lhs: arena.slot(*index as usize),
                    rhs: arena.alloc(Expression::ConstInt(*value as i32)),
                    op: BinOp::Add,
                }),
            ));
        }
        IIncW { index, value } => {
            stmts.push(assign(
                arena.slot(*index as usize),
                arena.alloc(Expression::BinOp {
                    lhs: arena.slot(*index as usize),
                    rhs: arena.alloc(Expression::ConstInt(*value as i32)),
                    op: BinOp::Add,
                }),
            ));
        }
        InstanceOf { index } => {
            let object = stack.pop()?;
            stmts.push(stack.push(arena.alloc(Expression::InstanceOf {
                object,
                class: Str(pool.retrieve(*index)?.name),
            })));
        }
        JSr { .. } | JSrW { .. } | Ret { .. } | RetW { .. } => {
            unreachable!("pre-parsing should have errored out on these instructions");
        }
        MonitorEnter => stmts.push(Statement::Basic(BasicStatement::MonitorEnter {
            object: stack.pop()?,
        })),
        MonitorExit => stmts.push(Statement::Basic(BasicStatement::MonitorExit {
            object: stack.pop()?,
        })),
        New { index } => {
            stmts.push(stack.push(arena.alloc(Expression::NewUninitialized {
                class: Str(pool.retrieve(*index)?.name),
            })));
        }
        NewArray { atype } => {
            let length = stack.pop()?;
            stmts.push(stack.push(arena.alloc(Expression::NewArray {
                element_type: Type::Primitive(match atype {
                    ArrayType::Boolean | ArrayType::Byte => PrimitiveType::Byte,
                    ArrayType::Char => PrimitiveType::Char,
                    ArrayType::Float => PrimitiveType::Float,
                    ArrayType::Double => PrimitiveType::Double,
                    ArrayType::Short => PrimitiveType::Short,
                    ArrayType::Int => PrimitiveType::Int,
                    ArrayType::Long => PrimitiveType::Long,
                }),
                lengths: vec![length],
            })));
        }
        Nop => {}
    }

    Ok(())
}
