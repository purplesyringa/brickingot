use super::{
    Statement,
    abstract_eval::{Machine, StackUnderflowError},
};
use crate::ClassInfo;
use crate::ast::{
    Arena, BasicStatement, BinOp, CallKind, ExprId, Expression, PrimitiveType, Str, Type, UnaryOp,
};
use noak::{
    error::DecodeError,
    reader::{
        attributes::{
            ArrayType,
            RawInstruction::{self, *},
        },
        cpool::{
            self, ConstantPool, Dynamic, Index, InterfaceMethodRef, Item, MethodHandle, MethodRef,
            value::FieldRef,
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

// Low-level assign: invalid if `target` was produced by `machine.get_*`.
#[must_use = "returns a statement that needs to be emitted manually"]
fn ll_assign(target: ExprId, value: ExprId) -> Statement {
    Statement::Basic(BasicStatement::Assign { target, value })
}

fn field<'code>(arena: &Arena<'code>, object: Option<ExprId>, field: &FieldRef<'code>) -> ExprId {
    arena.alloc(Expression::Field {
        object,
        class: Str(field.class.name),
        name: Str(field.name_and_type.name),
        descriptor: Str(field.name_and_type.descriptor),
    })
}

fn invoke<'arena, 'code>(
    class_info: &mut ClassInfo<'code>,
    pool: &ConstantPool<'code>,
    machine: &mut Machine<'arena, 'code>,
    index: Index<Item<'code>>,
    has_receiver: bool,
    is_special: bool,
) -> Result<(), InsnIrImportError> {
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

    let method_descriptor = class_info.get_method_descriptor(*name_and_type)?;
    let name_and_type = pool.retrieve(*name_and_type)?;
    let class_or_interface = Str(pool.retrieve(*class)?.name);
    let arguments = machine.pop_method_arguments(&method_descriptor.descriptor)?;

    let kind = if has_receiver {
        CallKind::Method {
            class_or_interface,
            object: machine.pop()?,
            is_special,
        }
    } else {
        CallKind::Static { class_or_interface }
    };

    machine.push_return_type(
        &method_descriptor.descriptor.return_type(),
        machine.arena.alloc(Expression::Call {
            method_name: Str(name_and_type.name),
            kind,
            arguments,
            descriptor: Str(name_and_type.descriptor),
        }),
    );
    Ok(())
}

pub fn import_insn_to_ir<'arena, 'code>(
    class_info: &mut ClassInfo<'code>,
    machine: &mut Machine<'arena, 'code>,
    pool: &ConstantPool<'code>,
    address: u32,
    insn: &RawInstruction<'code>,
) -> Result<(), InsnIrImportError> {
    let arena = machine.arena;

    let offset_to_bb_id = |machine: &mut Machine<'arena, 'code>, offset: i32| -> usize {
        let address = (address as i32 + offset) as u32;
        *machine
            .address_to_bb_id
            .get(&address)
            .expect("invalid jump target")
    };

    let jump = |machine: &mut Machine<'arena, 'code>, condition: ExprId, offset: i32| {
        let target = offset_to_bb_id(machine, offset);
        machine.flush_stack_writes();
        machine.add(Statement::Jump { condition, target });
    };

    match insn {
        // Array loads/stores
        AALoad | BALoad | CALoad | FALoad | IALoad | SALoad => {
            let index = machine.pop()?;
            let array = machine.pop()?;
            machine.push(arena.alloc(Expression::ArrayElement { array, index }));
        }
        DALoad | LALoad => {
            let index = machine.pop()?;
            let array = machine.pop()?;
            machine.push2(arena.alloc(Expression::ArrayElement { array, index }));
        }
        AAStore | BAStore | CAStore | FAStore | IAStore | SAStore => {
            let value = machine.pop()?;
            let index = machine.pop()?;
            let array = machine.pop()?;
            machine.add(ll_assign(
                arena.alloc(Expression::ArrayElement { array, index }),
                value,
            ));
        }
        DAStore | LAStore => {
            let value = machine.pop2()?;
            let index = machine.pop()?;
            let array = machine.pop()?;
            machine.add(ll_assign(
                arena.alloc(Expression::ArrayElement { array, index }),
                value,
            ));
        }

        // Slot load/stores
        ALoad { index } | FLoad { index } | ILoad { index } => {
            let value = machine.get_slot(*index as usize);
            machine.push(value);
        }
        ALoadW { index } | FLoadW { index } | ILoadW { index } => {
            let value = machine.get_slot(*index as usize);
            machine.push(value);
        }
        DLoad { index } | LLoad { index } => {
            let value = machine.get_slot(*index as usize);
            machine.push2(value);
        }
        DLoadW { index } | LLoadW { index } => {
            let value = machine.get_slot(*index as usize);
            machine.push2(value);
        }
        ALoad0 | FLoad0 | ILoad0 => {
            let value = machine.get_slot(0);
            machine.push(value);
        }
        ALoad1 | FLoad1 | ILoad1 => {
            let value = machine.get_slot(1);
            machine.push(value);
        }
        ALoad2 | FLoad2 | ILoad2 => {
            let value = machine.get_slot(2);
            machine.push(value);
        }
        ALoad3 | FLoad3 | ILoad3 => {
            let value = machine.get_slot(3);
            machine.push(value);
        }
        DLoad0 | LLoad0 => {
            let value = machine.get_slot(0);
            machine.push2(value);
        }
        DLoad1 | LLoad1 => {
            let value = machine.get_slot(1);
            machine.push2(value);
        }
        DLoad2 | LLoad2 => {
            let value = machine.get_slot(2);
            machine.push2(value);
        }
        DLoad3 | LLoad3 => {
            let value = machine.get_slot(3);
            machine.push2(value);
        }

        AStore { index } | FStore { index } | IStore { index } => {
            let value = machine.pop()?;
            machine.set_slot(*index as usize, value);
        }
        AStoreW { index } | FStoreW { index } | IStoreW { index } => {
            let value = machine.pop()?;
            machine.set_slot(*index as usize, value);
        }
        DStore { index } | LStore { index } => {
            let value = machine.pop2()?;
            machine.set_slot(*index as usize, value);
        }
        DStoreW { index } | LStoreW { index } => {
            let value = machine.pop2()?;
            machine.set_slot(*index as usize, value);
        }
        AStore0 | FStore0 | IStore0 => {
            let value = machine.pop()?;
            machine.set_slot(0, value);
        }
        AStore1 | FStore1 | IStore1 => {
            let value = machine.pop()?;
            machine.set_slot(1, value);
        }
        AStore2 | FStore2 | IStore2 => {
            let value = machine.pop()?;
            machine.set_slot(2, value);
        }
        AStore3 | FStore3 | IStore3 => {
            let value = machine.pop()?;
            machine.set_slot(3, value);
        }
        DStore0 | LStore0 => {
            let value = machine.pop2()?;
            machine.set_slot(0, value);
        }
        DStore1 | LStore1 => {
            let value = machine.pop2()?;
            machine.set_slot(1, value);
        }
        DStore2 | LStore2 => {
            let value = machine.pop2()?;
            machine.set_slot(2, value);
        }
        DStore3 | LStore3 => {
            let value = machine.pop2()?;
            machine.set_slot(3, value);
        }

        // Constants
        AConstNull => machine.push(arena.null()),
        BIPush { value } => machine.push(arena.alloc(Expression::ConstByte(*value))),
        SIPush { value } => machine.push(arena.alloc(Expression::ConstShort(*value))),
        FConst0 => machine.push(arena.alloc(Expression::ConstFloat(0.0))),
        FConst1 => machine.push(arena.alloc(Expression::ConstFloat(1.0))),
        FConst2 => machine.push(arena.alloc(Expression::ConstFloat(2.0))),
        IConstM1 => machine.push(arena.alloc(Expression::ConstInt(-1))),
        IConst0 => machine.push(arena.alloc(Expression::ConstInt(0))),
        IConst1 => machine.push(arena.alloc(Expression::ConstInt(1))),
        IConst2 => machine.push(arena.alloc(Expression::ConstInt(2))),
        IConst3 => machine.push(arena.alloc(Expression::ConstInt(3))),
        IConst4 => machine.push(arena.alloc(Expression::ConstInt(4))),
        IConst5 => machine.push(arena.alloc(Expression::ConstInt(5))),
        DConst0 => machine.push2(arena.alloc(Expression::ConstDouble(0.0))),
        DConst1 => machine.push2(arena.alloc(Expression::ConstDouble(1.0))),
        LConst0 => machine.push2(arena.alloc(Expression::ConstLong(0))),
        LConst1 => machine.push2(arena.alloc(Expression::ConstLong(1))),
        LdC { index } | LdCW { index } => match pool.get(*index)? {
            Item::Integer(cpool::Integer { value }) => {
                machine.push(arena.alloc(Expression::ConstInt(*value)));
            }
            Item::Float(cpool::Float { value }) => {
                machine.push(arena.alloc(Expression::ConstFloat(*value)));
            }
            Item::Class(cpool::Class { name }) => {
                machine.push(arena.alloc(Expression::Class(Str(pool.retrieve(*name)?))));
            }
            Item::String(cpool::String { string }) => {
                machine.push(arena.alloc(Expression::ConstString(pool.retrieve(*string)?)));
            }
            Item::MethodHandle(_) => machine.push(arena.alloc(Expression::ConstMethodHandle(
                pool.retrieve(Index::<MethodHandle>::new(index.as_u16()).unwrap())?,
            ))),
            Item::MethodType(cpool::MethodType { descriptor }) => {
                machine.push(arena.alloc(Expression::ConstMethodType {
                    descriptor: pool.retrieve(*descriptor)?,
                }));
            }
            Item::Dynamic(_) => machine.push(arena.alloc(Expression::DynamicConst(
                pool.retrieve(Index::<Dynamic>::new(index.as_u16()).unwrap())?,
            ))),
            _ => return Err(InsnIrImportError::InvalidLdc),
        },
        LdC2W { index } => match pool.get(*index)? {
            Item::Long(cpool::Long { value }) => {
                machine.push2(arena.alloc(Expression::ConstLong(*value)));
            }
            Item::Double(cpool::Double { value }) => {
                machine.push2(arena.alloc(Expression::ConstDouble(*value)));
            }
            _ => return Err(InsnIrImportError::InvalidLdc2),
        },

        // Conversions
        CheckCast { index } => {
            let object = machine.pop()?;
            machine.push(arena.alloc(Expression::CastReference {
                object,
                class: Str(pool.retrieve(*index)?.name),
            }));
        }
        D2F => machine.cast_primitive(PrimitiveType::Double, PrimitiveType::Float)?,
        D2I => machine.cast_primitive(PrimitiveType::Double, PrimitiveType::Int)?,
        D2L => machine.cast_primitive(PrimitiveType::Double, PrimitiveType::Long)?,
        F2D => machine.cast_primitive(PrimitiveType::Float, PrimitiveType::Double)?,
        F2I => machine.cast_primitive(PrimitiveType::Float, PrimitiveType::Int)?,
        F2L => machine.cast_primitive(PrimitiveType::Float, PrimitiveType::Long)?,
        I2B => machine.cast_primitive(PrimitiveType::Int, PrimitiveType::Byte)?,
        I2C => machine.cast_primitive(PrimitiveType::Int, PrimitiveType::Char)?,
        I2D => machine.cast_primitive(PrimitiveType::Int, PrimitiveType::Double)?,
        I2F => machine.cast_primitive(PrimitiveType::Int, PrimitiveType::Float)?,
        I2L => machine.cast_primitive(PrimitiveType::Int, PrimitiveType::Long)?,
        I2S => machine.cast_primitive(PrimitiveType::Int, PrimitiveType::Short)?,
        L2D => machine.cast_primitive(PrimitiveType::Long, PrimitiveType::Double)?,
        L2F => machine.cast_primitive(PrimitiveType::Long, PrimitiveType::Float)?,
        L2I => machine.cast_primitive(PrimitiveType::Long, PrimitiveType::Int)?,

        // Arithmetic
        DAdd => machine.arith_binop(BinOp::Add, PrimitiveType::Double)?,
        DSub => machine.arith_binop(BinOp::Sub, PrimitiveType::Double)?,
        DMul => machine.arith_binop(BinOp::Mul, PrimitiveType::Double)?,
        DDiv => machine.arith_binop(BinOp::Div { is_fp: true }, PrimitiveType::Double)?,
        DRem => machine.arith_binop(BinOp::Rem { is_fp: true }, PrimitiveType::Double)?,
        FAdd => machine.arith_binop(BinOp::Add, PrimitiveType::Float)?,
        FSub => machine.arith_binop(BinOp::Sub, PrimitiveType::Float)?,
        FMul => machine.arith_binop(BinOp::Mul, PrimitiveType::Float)?,
        FDiv => machine.arith_binop(BinOp::Div { is_fp: true }, PrimitiveType::Float)?,
        FRem => machine.arith_binop(BinOp::Rem { is_fp: true }, PrimitiveType::Float)?,
        IAdd => machine.arith_binop(BinOp::Add, PrimitiveType::Int)?,
        ISub => machine.arith_binop(BinOp::Sub, PrimitiveType::Int)?,
        IMul => machine.arith_binop(BinOp::Mul, PrimitiveType::Int)?,
        IDiv => machine.arith_binop(BinOp::Div { is_fp: false }, PrimitiveType::Int)?,
        IRem => machine.arith_binop(BinOp::Rem { is_fp: false }, PrimitiveType::Int)?,
        LAdd => machine.arith_binop(BinOp::Add, PrimitiveType::Long)?,
        LSub => machine.arith_binop(BinOp::Sub, PrimitiveType::Long)?,
        LMul => machine.arith_binop(BinOp::Mul, PrimitiveType::Long)?,
        LDiv => machine.arith_binop(BinOp::Div { is_fp: false }, PrimitiveType::Long)?,
        LRem => machine.arith_binop(BinOp::Rem { is_fp: false }, PrimitiveType::Long)?,
        IAnd => machine.arith_binop(BinOp::And, PrimitiveType::Int)?,
        IOr => machine.arith_binop(BinOp::Or, PrimitiveType::Int)?,
        IXor => machine.arith_binop(BinOp::Xor, PrimitiveType::Int)?,
        LAnd => machine.arith_binop(BinOp::And, PrimitiveType::Long)?,
        LOr => machine.arith_binop(BinOp::Or, PrimitiveType::Long)?,
        LXor => machine.arith_binop(BinOp::Xor, PrimitiveType::Long)?,
        IShL => machine.arith_binop(BinOp::Shl, PrimitiveType::Int)?,
        IShR => machine.arith_binop(BinOp::Shr, PrimitiveType::Int)?,
        IUShR => machine.arith_binop(BinOp::UnsignedShr, PrimitiveType::Int)?,
        LShL => machine.binop(
            BinOp::Shl,
            PrimitiveType::Long,
            PrimitiveType::Long,
            PrimitiveType::Int,
        )?,
        LShR => machine.binop(
            BinOp::Shr,
            PrimitiveType::Long,
            PrimitiveType::Long,
            PrimitiveType::Int,
        )?,
        LUShR => machine.binop(
            BinOp::UnsignedShr,
            PrimitiveType::Long,
            PrimitiveType::Long,
            PrimitiveType::Int,
        )?,
        DCmpG => machine.binop(
            BinOp::Compare {
                fp_negative_on_nan: false,
            },
            PrimitiveType::Int,
            PrimitiveType::Double,
            PrimitiveType::Double,
        )?,
        DCmpL => machine.binop(
            BinOp::Compare {
                fp_negative_on_nan: true,
            },
            PrimitiveType::Int,
            PrimitiveType::Double,
            PrimitiveType::Double,
        )?,
        FCmpG => machine.binop(
            BinOp::Compare {
                fp_negative_on_nan: false,
            },
            PrimitiveType::Int,
            PrimitiveType::Float,
            PrimitiveType::Float,
        )?,
        FCmpL => machine.binop(
            BinOp::Compare {
                fp_negative_on_nan: true,
            },
            PrimitiveType::Int,
            PrimitiveType::Float,
            PrimitiveType::Float,
        )?,
        LCmp => machine.binop(
            BinOp::Compare {
                fp_negative_on_nan: false,
            },
            PrimitiveType::Int,
            PrimitiveType::Long,
            PrimitiveType::Long,
        )?,
        DNeg | LNeg => {
            let argument = machine.pop2()?;
            machine.push2(arena.alloc(Expression::UnaryOp {
                argument,
                op: UnaryOp::Neg,
            }));
        }
        FNeg | INeg => {
            let argument = machine.pop()?;
            machine.push(arena.alloc(Expression::UnaryOp {
                argument,
                op: UnaryOp::Neg,
            }));
        }

        // Stack manipulation. All of these need to use `copy` instead of `pop`/`push` even if
        // applicable so that merging understands these operations can't have side effects and can
        // be optimized out.
        Dup => {
            if machine.stack_size < 1 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            machine.copy(machine.stack_size, machine.stack_size - 1);
            machine.stack_size += 1;
        }
        DupX1 => {
            if machine.stack_size < 2 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            // Can't just clone Expression because variables will get reassigned and we don't have
            // SSA yet, need to perform something similar to a temporary-variable swap instead.
            machine.copy(machine.stack_size, machine.stack_size - 1);
            machine.copy(machine.stack_size - 1, machine.stack_size - 2);
            machine.copy(machine.stack_size - 2, machine.stack_size);
            machine.stack_size += 1;
        }
        DupX2 => {
            if machine.stack_size < 3 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            machine.copy(machine.stack_size, machine.stack_size - 1);
            machine.copy(machine.stack_size - 1, machine.stack_size - 2);
            machine.copy(machine.stack_size - 2, machine.stack_size - 3);
            machine.copy(machine.stack_size - 3, machine.stack_size);
            machine.stack_size += 1;
        }
        Dup2 => {
            if machine.stack_size < 2 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            machine.copy(machine.stack_size, machine.stack_size - 2);
            machine.copy(machine.stack_size + 1, machine.stack_size - 1);
            machine.stack_size += 2;
        }
        Dup2X1 => {
            if machine.stack_size < 3 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            machine.copy(machine.stack_size + 1, machine.stack_size - 1);
            machine.copy(machine.stack_size, machine.stack_size - 2);
            machine.copy(machine.stack_size - 1, machine.stack_size - 3);
            machine.copy(machine.stack_size - 2, machine.stack_size + 1);
            machine.copy(machine.stack_size - 3, machine.stack_size);
            machine.stack_size += 2;
        }
        Dup2X2 => {
            if machine.stack_size < 4 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            machine.copy(machine.stack_size + 1, machine.stack_size - 1);
            machine.copy(machine.stack_size, machine.stack_size - 2);
            machine.copy(machine.stack_size - 1, machine.stack_size - 3);
            machine.copy(machine.stack_size - 2, machine.stack_size - 4);
            machine.copy(machine.stack_size - 3, machine.stack_size + 1);
            machine.copy(machine.stack_size - 4, machine.stack_size);
            machine.stack_size += 2;
        }
        Pop => {
            if machine.stack_size < 1 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            machine.stack_size -= 1;
        }
        Pop2 => {
            if machine.stack_size < 2 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            machine.stack_size -= 2;
        }
        Swap => {
            if machine.stack_size < 2 {
                return Err(InsnIrImportError::StackUnderflow(StackUnderflowError));
            }
            // Use `usize::MAX` as a temporary so that linking can see through this swap.
            machine.copy(usize::MAX, machine.stack_size - 1);
            machine.copy(machine.stack_size - 1, machine.stack_size - 2);
            machine.copy(machine.stack_size - 2, usize::MAX);
        }

        // Exits
        AThrow => {
            let exception = machine.pop()?;
            machine.drop_stack_writes();
            machine.add(Statement::Basic(BasicStatement::Throw { exception }));
        }
        AReturn | FReturn | IReturn => {
            let value = machine.pop()?;
            machine.drop_stack_writes();
            machine.add(Statement::Basic(BasicStatement::Return { value }));
        }
        DReturn | LReturn => {
            let value = machine.pop2()?;
            machine.drop_stack_writes();
            machine.add(Statement::Basic(BasicStatement::Return { value }));
        }
        Return => {
            machine.drop_stack_writes();
            machine.add(Statement::Basic(BasicStatement::ReturnVoid));
        }

        // Jumps
        Goto { offset } => jump(machine, arena.int(1), *offset as i32),
        GotoW { offset } => jump(machine, arena.int(1), *offset),
        IfACmpEq { offset } => {
            let rhs = machine.pop()?;
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Eq,
                }),
                *offset as i32,
            );
        }
        IfACmpNe { offset } => {
            let rhs = machine.pop()?;
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Ne,
                }),
                *offset as i32,
            );
        }
        IfICmpEq { offset } => {
            let rhs = machine.pop()?;
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Eq,
                }),
                *offset as i32,
            );
        }
        IfICmpNe { offset } => {
            let rhs = machine.pop()?;
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Ne,
                }),
                *offset as i32,
            );
        }
        IfICmpLt { offset } => {
            let rhs = machine.pop()?;
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Lt,
                }),
                *offset as i32,
            );
        }
        IfICmpGe { offset } => {
            let rhs = machine.pop()?;
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Ge,
                }),
                *offset as i32,
            );
        }
        IfICmpGt { offset } => {
            let rhs = machine.pop()?;
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Gt,
                }),
                *offset as i32,
            );
        }
        IfICmpLe { offset } => {
            let rhs = machine.pop()?;
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Le,
                }),
                *offset as i32,
            );
        }
        IfEq { offset } => {
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs: arena.int(0),
                    op: BinOp::Eq,
                }),
                *offset as i32,
            );
        }
        IfNe { offset } => {
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs: arena.int(0),
                    op: BinOp::Ne,
                }),
                *offset as i32,
            );
        }
        IfLt { offset } => {
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs: arena.int(0),
                    op: BinOp::Lt,
                }),
                *offset as i32,
            );
        }
        IfGe { offset } => {
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs: arena.int(0),
                    op: BinOp::Ge,
                }),
                *offset as i32,
            );
        }
        IfGt { offset } => {
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs: arena.int(0),
                    op: BinOp::Gt,
                }),
                *offset as i32,
            );
        }
        IfLe { offset } => {
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs: arena.int(0),
                    op: BinOp::Le,
                }),
                *offset as i32,
            );
        }
        IfNonNull { offset } => {
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs: arena.null(),
                    op: BinOp::Ne,
                }),
                *offset as i32,
            );
        }
        IfNull { offset } => {
            let lhs = machine.pop()?;
            jump(
                machine,
                arena.alloc(Expression::BinOp {
                    lhs,
                    rhs: arena.null(),
                    op: BinOp::Eq,
                }),
                *offset as i32,
            );
        }
        LookupSwitch(switch) => {
            let key = machine.pop()?;
            let arms = switch
                .pairs()
                .map(|pair| (pair.key(), offset_to_bb_id(machine, pair.offset())))
                .collect();
            let default = offset_to_bb_id(machine, switch.default_offset());
            machine.flush_stack_writes();
            machine.add(Statement::Switch { key, arms, default });
        }
        TableSwitch(switch) => {
            let key = machine.pop()?;
            let arms = switch
                .pairs()
                .map(|pair| (pair.key(), offset_to_bb_id(machine, pair.offset())))
                .collect();
            let default = offset_to_bb_id(machine, switch.default_offset());
            machine.flush_stack_writes();
            machine.add(Statement::Switch { key, arms, default });
        }

        // Function calls
        InvokeDynamic { index } => {
            let indy = pool.get(*index)?;
            let method_descriptor = &class_info
                .get_method_descriptor(indy.name_and_type)?
                .descriptor;
            let name_and_type = pool.retrieve(indy.name_and_type)?;
            let arguments = machine.pop_method_arguments(method_descriptor)?;
            machine.push_return_type(
                &method_descriptor.return_type(),
                arena.alloc(Expression::Call {
                    method_name: Str(name_and_type.name),
                    kind: CallKind::Dynamic {
                        bootstrap_method_attr: indy.bootstrap_method_attr,
                    },
                    arguments,
                    descriptor: Str(name_and_type.descriptor),
                }),
            );
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
            invoke(
                class_info,
                pool,
                machine,
                Index::new(index.as_u16()).unwrap(),
                true,
                true,
            )?;
        }
        InvokeStatic { index } => invoke(class_info, pool, machine, *index, false, false)?,
        InvokeInterface { index, .. } => invoke(
            class_info,
            pool,
            machine,
            Index::new(index.as_u16()).unwrap(),
            true,
            false,
        )?,
        InvokeVirtual { index } => invoke(
            class_info,
            pool,
            machine,
            Index::new(index.as_u16()).unwrap(),
            true,
            false,
        )?,

        // Field operations
        GetField { index } => {
            let field_ref = pool.retrieve(*index)?;
            let object = machine.pop()?;
            machine.push_nat(
                &field_ref.name_and_type,
                field(arena, Some(object), &field_ref),
            );
        }
        GetStatic { index } => {
            let field_ref = pool.retrieve(*index)?;
            machine.push_nat(&field_ref.name_and_type, field(arena, None, &field_ref));
        }
        PutField { index } => {
            let field_ref = pool.retrieve(*index)?;
            let value = machine.pop_nat(&field_ref.name_and_type)?;
            let object = machine.pop()?;
            machine.add(ll_assign(field(arena, Some(object), &field_ref), value));
        }
        PutStatic { index } => {
            let field_ref = pool.retrieve(*index)?;
            let value = machine.pop_nat(&field_ref.name_and_type)?;
            machine.add(ll_assign(field(arena, None, &field_ref), value));
        }

        // Miscellaneous
        ANewArray { index } => {
            let length = machine.pop()?;
            machine.push(arena.alloc(Expression::NewArray {
                element_type: Type::Reference(Str(pool.retrieve(*index)?.name)),
                lengths: vec![length],
            }));
        }
        ArrayLength => {
            let array = machine.pop()?;
            machine.push(arena.alloc(Expression::ArrayLength { array }));
        }
        MultiANewArray { index, dimensions } => {
            let mut lengths: Vec<ExprId> = (0..*dimensions)
                .map(|_| machine.pop())
                .collect::<Result<_, _>>()?;
            lengths.reverse();
            machine.push(arena.alloc(Expression::NewArray {
                element_type: Type::Reference(Str(pool.retrieve(*index)?.name)),
                lengths,
            }));
        }
        IInc { index, value } => {
            let value = arena.alloc(Expression::BinOp {
                lhs: machine.get_slot(*index as usize),
                rhs: arena.alloc(Expression::ConstInt(*value as i32)),
                op: BinOp::Add,
            });
            machine.set_slot(*index as usize, value);
        }
        IIncW { index, value } => {
            let value = arena.alloc(Expression::BinOp {
                lhs: machine.get_slot(*index as usize),
                rhs: arena.alloc(Expression::ConstInt(*value as i32)),
                op: BinOp::Add,
            });
            machine.set_slot(*index as usize, value);
        }
        InstanceOf { index } => {
            let object = machine.pop()?;
            machine.push(arena.alloc(Expression::InstanceOf {
                object,
                class: Str(pool.retrieve(*index)?.name),
            }));
        }
        JSr { .. } | JSrW { .. } | Ret { .. } | RetW { .. } => {
            unreachable!("pre-parsing should have errored out on these instructions");
        }
        MonitorEnter => {
            let object = machine.pop()?;
            machine.add(Statement::Basic(BasicStatement::MonitorEnter { object }));
        }
        MonitorExit => {
            let object = machine.pop()?;
            machine.add(Statement::Basic(BasicStatement::MonitorExit { object }));
        }
        New { index } => {
            machine.push(arena.alloc(Expression::NewUninitialized {
                class: Str(pool.retrieve(*index)?.name),
            }));
        }
        NewArray { atype } => {
            let length = machine.pop()?;
            machine.push(arena.alloc(Expression::NewArray {
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
            }));
        }
        Nop => {}
    }

    Ok(())
}
