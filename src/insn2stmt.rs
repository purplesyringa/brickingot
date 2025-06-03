use crate::ast::{
    Arguments, BasicStatement, BinOp, Call, CallKind, Expression, Field, PrimitiveType, Str, Type,
    UnaryOp, VariableNamespace,
};
use crate::instructions::{is_double_width, is_type_descriptor_double_width};
use crate::unstructured::{Statement, Switch};
use noak::{
    descriptor::{MethodDescriptor, TypeDescriptor},
    error::DecodeError,
    reader::{
        attributes::{ArrayType, RawInstruction},
        cpool::{
            self, ConstantPool, Dynamic, Index, InterfaceMethodRef, Item, MethodHandle, MethodRef,
            value::{FieldRef, NameAndType},
        },
    },
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum InstructionParseError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("Accessed more elements than there are in the stack")]
    StackUnderflow,

    #[error("ldc instruction accessed a constant of an invalid type")]
    InvalidLdc,

    #[error("ldc2 instruction accessed a constant of an invalid type")]
    InvalidLdc2,

    #[error("Bootstrap method index is out-of-bounds")]
    BootstrapMethodIndexOutOfBounds,
}

struct StackMachine {
    stack_size: usize,
}

impl StackMachine {
    fn pop_sized<'a>(&mut self, size: usize) -> Result<Box<Expression<'a>>, InstructionParseError> {
        if self.stack_size < size {
            return Err(InstructionParseError::StackUnderflow);
        }
        self.stack_size -= size;
        Ok(Box::new(Expression::Variable {
            id: self.stack_size,
            namespace: VariableNamespace::Stack,
        }))
    }

    fn pop<'a>(&mut self) -> Result<Box<Expression<'a>>, InstructionParseError> {
        self.pop_sized(1)
    }

    fn pop2<'a>(&mut self) -> Result<Box<Expression<'a>>, InstructionParseError> {
        self.pop_sized(2)
    }

    fn pop_method_arguments<'a>(
        &mut self,
        method_descriptor: &MethodDescriptor<'a>,
    ) -> Result<Arguments<'a>, InstructionParseError> {
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
        Ok(Arguments(
            parameter_sizes
                .iter()
                .rev()
                .map(|size| self.pop_sized(*size))
                .collect::<Result<_, _>>()?,
        ))
    }

    fn pop_nat<'a>(
        &mut self,
        name_and_type: &NameAndType<'a>,
    ) -> Result<Box<Expression<'a>>, InstructionParseError> {
        if is_double_width(name_and_type) {
            self.pop2()
        } else {
            self.pop()
        }
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    fn push_sized<'a>(&mut self, size: usize, value: Box<Expression<'a>>) -> Statement<'a> {
        let id = self.stack_size;
        self.stack_size += size;
        Statement::Basic(BasicStatement::Assign {
            target: Box::new(Expression::Variable {
                id,
                namespace: VariableNamespace::Stack,
            }),
            value,
        })
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    fn push<'a>(&mut self, value: Box<Expression<'a>>) -> Statement<'a> {
        self.push_sized(1, value)
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    fn push2<'a>(&mut self, value: Box<Expression<'a>>) -> Statement<'a> {
        self.push_sized(2, value)
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    fn push_return_type<'a>(
        &mut self,
        return_type: &Option<TypeDescriptor<'a>>,
        value: Box<Expression<'a>>,
    ) -> Statement<'a> {
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
    fn push_nat<'a>(
        &mut self,
        name_and_type: &NameAndType<'a>,
        value: Box<Expression<'a>>,
    ) -> Statement<'a> {
        if is_double_width(name_and_type) {
            self.push2(value)
        } else {
            self.push(value)
        }
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    fn cast_primitive<'a>(
        &mut self,
        from: PrimitiveType,
        to: PrimitiveType,
    ) -> Result<Statement<'a>, InstructionParseError> {
        let value = self.pop_sized(from.size())?;
        Ok(self.push_sized(
            to.size(),
            Box::new(Expression::CastPrimitive { value, from, to }),
        ))
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    fn binop<'a>(
        &mut self,
        op: BinOp,
        res_ty: PrimitiveType,
        lhs_ty: PrimitiveType,
        rhs_ty: PrimitiveType,
    ) -> Result<Statement<'a>, InstructionParseError> {
        let rhs = self.pop_sized(rhs_ty.size())?;
        let lhs = self.pop_sized(lhs_ty.size())?;
        Ok(self.push_sized(res_ty.size(), Box::new(Expression::BinOp { lhs, rhs, op })))
    }

    #[must_use = "returns a statement that needs to be emitted manually"]
    fn arith_binop<'a>(
        &mut self,
        op: BinOp,
        ty: PrimitiveType,
    ) -> Result<Statement<'a>, InstructionParseError> {
        self.binop(op, ty, ty, ty)
    }
}

#[must_use = "returns a statement that needs to be emitted manually"]
fn assign<'a>(target: Box<Expression<'a>>, value: Box<Expression<'a>>) -> Statement<'a> {
    Statement::Basic(BasicStatement::Assign { target, value })
}

#[must_use = "returns a statement that needs to be emitted manually"]
fn assign_at_stack<'a>(target: usize, source: usize) -> Statement<'a> {
    assign(at_stack(target), at_stack(source))
}

fn slot<'a>(id: usize) -> Box<Expression<'a>> {
    Box::new(Expression::Variable {
        id,
        namespace: VariableNamespace::Slot,
    })
}

fn at_stack<'a>(id: usize) -> Box<Expression<'a>> {
    Box::new(Expression::Variable {
        id,
        namespace: VariableNamespace::Stack,
    })
}

fn tmp<'a>(id: usize) -> Box<Expression<'a>> {
    Box::new(Expression::Variable {
        id,
        namespace: VariableNamespace::Temporary,
    })
}

fn zero<'a>() -> Box<Expression<'a>> {
    Box::new(Expression::ConstInt(0))
}

fn one<'a>() -> Box<Expression<'a>> {
    Box::new(Expression::ConstInt(1))
}

fn null<'a>() -> Box<Expression<'a>> {
    Box::new(Expression::Null)
}

fn field<'a>(object: Option<Box<Expression<'a>>>, field: &FieldRef<'a>) -> Box<Expression<'a>> {
    Box::new(Expression::Field(Field {
        object,
        class: Str(field.class.name),
        name: Str(field.name_and_type.name),
        descriptor: Str(field.name_and_type.descriptor),
    }))
}

pub fn convert_instruction_to_unstructured_ast<'a>(
    pool: &ConstantPool<'a>,
    address: u32,
    stack_size: usize,
    insn: &RawInstruction<'a>,
    stmts: &mut Vec<Statement<'a>>,
) -> Result<(), InstructionParseError> {
    use RawInstruction::*;

    // Double-width slots and stack elements (i.e. long/double) are simulated by storing the whole
    // value in the first slot and ignoring the second slot, rather than explicitly splitting the
    // values. Such an interpretation is valid for class files that pass verification, and we don't
    // care about handling classes that don't exactly correctly (our behavior is still reasonable,
    // but a legacy JVM implementation without verification might handle code differently than the
    // way we decompile it).

    let mut stack = StackMachine { stack_size };

    let offset_to_address = |offset: i32| -> u32 { (address as i32 + offset) as u32 };

    let jump = |condition: Box<Expression<'a>>, offset: i32| -> Statement<'a> {
        Statement::Jump {
            condition,
            // The preparsing steps ensures all goto destinations are valid instruction addresses.
            // This will be replaced by the instruction index on a later pass, after all
            // instructions are emitted.
            target: offset_to_address(offset) as usize,
        }
    };

    let invoke = |stack: &mut StackMachine,
                  index: Index<Item<'a>>,
                  has_receiver: bool,
                  is_special: bool|
     -> Result<Statement<'a>, InstructionParseError> {
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
            Box::new(Expression::Call(Call {
                method_name: Str(name_and_type.name),
                kind,
                arguments,
                descriptor: Str(name_and_type.descriptor),
            })),
        ))
    };

    match insn {
        // Array loads/stores
        AALoad | BALoad | CALoad | FALoad | IALoad | SALoad => {
            let index = stack.pop()?;
            let array = stack.pop()?;
            stmts.push(stack.push(Box::new(Expression::ArrayElement { array, index })));
        }
        DALoad | LALoad => {
            let index = stack.pop()?;
            let array = stack.pop()?;
            stmts.push(stack.push2(Box::new(Expression::ArrayElement { array, index })));
        }
        AAStore | BAStore | CAStore | FAStore | IAStore | SAStore => {
            let value = stack.pop()?;
            let index = stack.pop()?;
            let array = stack.pop()?;
            stmts.push(assign(
                Box::new(Expression::ArrayElement { array, index }),
                value,
            ));
        }
        DAStore | LAStore => {
            let value = stack.pop2()?;
            let index = stack.pop()?;
            let array = stack.pop()?;
            stmts.push(assign(
                Box::new(Expression::ArrayElement { array, index }),
                value,
            ));
        }

        // Slot load/stores
        ALoad { index } | FLoad { index } | ILoad { index } => {
            stmts.push(stack.push(slot(*index as usize)))
        }
        ALoadW { index } | FLoadW { index } | ILoadW { index } => {
            stmts.push(stack.push(slot(*index as usize)))
        }
        DLoad { index } | LLoad { index } => stmts.push(stack.push2(slot(*index as usize))),
        DLoadW { index } | LLoadW { index } => stmts.push(stack.push2(slot(*index as usize))),
        ALoad0 | FLoad0 | ILoad0 => stmts.push(stack.push(slot(0))),
        ALoad1 | FLoad1 | ILoad1 => stmts.push(stack.push(slot(1))),
        ALoad2 | FLoad2 | ILoad2 => stmts.push(stack.push(slot(2))),
        ALoad3 | FLoad3 | ILoad3 => stmts.push(stack.push(slot(3))),
        DLoad0 | LLoad0 => stmts.push(stack.push2(slot(0))),
        DLoad1 | LLoad1 => stmts.push(stack.push2(slot(1))),
        DLoad2 | LLoad2 => stmts.push(stack.push2(slot(2))),
        DLoad3 | LLoad3 => stmts.push(stack.push2(slot(3))),

        AStore { index } | FStore { index } | IStore { index } => {
            stmts.push(assign(slot(*index as usize), stack.pop()?));
        }
        AStoreW { index } | FStoreW { index } | IStoreW { index } => {
            stmts.push(assign(slot(*index as usize), stack.pop()?));
        }
        DStore { index } | LStore { index } => {
            stmts.push(assign(slot(*index as usize), stack.pop2()?));
        }
        DStoreW { index } | LStoreW { index } => {
            stmts.push(assign(slot(*index as usize), stack.pop2()?));
        }
        AStore0 | FStore0 | IStore0 => stmts.push(assign(slot(0), stack.pop()?)),
        AStore1 | FStore1 | IStore1 => stmts.push(assign(slot(1), stack.pop()?)),
        AStore2 | FStore2 | IStore2 => stmts.push(assign(slot(2), stack.pop()?)),
        AStore3 | FStore3 | IStore3 => stmts.push(assign(slot(3), stack.pop()?)),
        DStore0 | LStore0 => stmts.push(assign(slot(0), stack.pop2()?)),
        DStore1 | LStore1 => stmts.push(assign(slot(1), stack.pop2()?)),
        DStore2 | LStore2 => stmts.push(assign(slot(2), stack.pop2()?)),
        DStore3 | LStore3 => stmts.push(assign(slot(3), stack.pop2()?)),

        // Constants
        AConstNull => stmts.push(stack.push(null())),
        BIPush { value } => stmts.push(stack.push(Box::new(Expression::ConstByte(*value)))),
        SIPush { value } => stmts.push(stack.push(Box::new(Expression::ConstShort(*value)))),
        FConst0 => stmts.push(stack.push(Box::new(Expression::ConstFloat(0.0)))),
        FConst1 => stmts.push(stack.push(Box::new(Expression::ConstFloat(1.0)))),
        FConst2 => stmts.push(stack.push(Box::new(Expression::ConstFloat(2.0)))),
        IConstM1 => stmts.push(stack.push(Box::new(Expression::ConstInt(-1)))),
        IConst0 => stmts.push(stack.push(Box::new(Expression::ConstInt(0)))),
        IConst1 => stmts.push(stack.push(Box::new(Expression::ConstInt(1)))),
        IConst2 => stmts.push(stack.push(Box::new(Expression::ConstInt(2)))),
        IConst3 => stmts.push(stack.push(Box::new(Expression::ConstInt(3)))),
        IConst4 => stmts.push(stack.push(Box::new(Expression::ConstInt(4)))),
        IConst5 => stmts.push(stack.push(Box::new(Expression::ConstInt(5)))),
        DConst0 => stmts.push(stack.push2(Box::new(Expression::ConstDouble(0.0)))),
        DConst1 => stmts.push(stack.push2(Box::new(Expression::ConstDouble(1.0)))),
        LConst0 => stmts.push(stack.push2(Box::new(Expression::ConstLong(0)))),
        LConst1 => stmts.push(stack.push2(Box::new(Expression::ConstLong(1)))),
        LdC { index } | LdCW { index } => match pool.get(*index)? {
            Item::Integer(cpool::Integer { value }) => {
                stmts.push(stack.push(Box::new(Expression::ConstInt(*value))))
            }
            Item::Float(cpool::Float { value }) => {
                stmts.push(stack.push(Box::new(Expression::ConstFloat(*value))))
            }
            Item::Class(cpool::Class { name }) => {
                stmts.push(stack.push(Box::new(Expression::Class(Str(pool.retrieve(*name)?)))))
            }
            Item::String(cpool::String { string }) => {
                stmts.push(stack.push(Box::new(Expression::ConstString(pool.retrieve(*string)?))))
            }
            Item::MethodHandle(_) => {
                stmts.push(stack.push(Box::new(Expression::ConstMethodHandle(
                    pool.retrieve(Index::<MethodHandle>::new(index.as_u16()).unwrap())?,
                ))))
            }
            Item::MethodType(cpool::MethodType { descriptor }) => {
                stmts.push(stack.push(Box::new(Expression::ConstMethodType {
                    descriptor: pool.retrieve(*descriptor)?,
                })))
            }
            Item::Dynamic(_) => stmts.push(stack.push(Box::new(Expression::DynamicConst(
                pool.retrieve(Index::<Dynamic>::new(index.as_u16()).unwrap())?,
            )))),
            _ => return Err(InstructionParseError::InvalidLdc),
        },
        LdC2W { index } => match pool.get(*index)? {
            Item::Long(cpool::Long { value }) => {
                stmts.push(stack.push(Box::new(Expression::ConstLong(*value))))
            }
            Item::Double(cpool::Double { value }) => {
                stmts.push(stack.push(Box::new(Expression::ConstDouble(*value))))
            }
            _ => return Err(InstructionParseError::InvalidLdc2),
        },

        // Conversions
        CheckCast { index } => {
            let value = stack.pop()?;
            stmts.push(stack.push(Box::new(Expression::CastReference {
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
        IDiv => stmts.push(stack.arith_binop(BinOp::Div { is_fp: true }, PrimitiveType::Int)?),
        IRem => stmts.push(stack.arith_binop(BinOp::Rem { is_fp: true }, PrimitiveType::Int)?),
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
            stmts.push(stack.push2(Box::new(Expression::UnaryOp {
                argument,
                op: UnaryOp::Neg,
            })));
        }
        FNeg | INeg => {
            let argument = stack.pop()?;
            stmts.push(stack.push(Box::new(Expression::UnaryOp {
                argument,
                op: UnaryOp::Neg,
            })));
        }

        // Stack manipulation
        Dup => {
            if stack.stack_size < 1 {
                return Err(InstructionParseError::StackUnderflow);
            }
            stmts.push(assign_at_stack(stack.stack_size, stack.stack_size - 1));
            stack.stack_size += 1;
        }
        DupX1 => {
            if stack.stack_size < 2 {
                return Err(InstructionParseError::StackUnderflow);
            }
            // Can't just clone Expression because variables will get reassigned and we don't have
            // SSA yet, need to perform something similar to a temporary-variable swap instead.
            stmts.extend([
                assign_at_stack(stack.stack_size, stack.stack_size - 1),
                assign_at_stack(stack.stack_size - 1, stack.stack_size - 2),
                assign_at_stack(stack.stack_size - 2, stack.stack_size),
            ]);
            stack.stack_size += 1;
        }
        DupX2 => {
            if stack.stack_size < 3 {
                return Err(InstructionParseError::StackUnderflow);
            }
            stmts.extend([
                assign_at_stack(stack.stack_size, stack.stack_size - 1),
                assign_at_stack(stack.stack_size - 1, stack.stack_size - 2),
                assign_at_stack(stack.stack_size - 2, stack.stack_size - 3),
                assign_at_stack(stack.stack_size - 3, stack.stack_size),
            ]);
            stack.stack_size += 1;
        }
        Dup2 => {
            if stack.stack_size < 2 {
                return Err(InstructionParseError::StackUnderflow);
            }
            stmts.push(assign_at_stack(stack.stack_size, stack.stack_size - 2));
            stack.stack_size += 2;
        }
        Dup2X1 => {
            if stack.stack_size < 3 {
                return Err(InstructionParseError::StackUnderflow);
            }
            stmts.extend([
                assign_at_stack(stack.stack_size + 1, stack.stack_size - 1),
                assign_at_stack(stack.stack_size, stack.stack_size - 2),
                assign_at_stack(stack.stack_size - 1, stack.stack_size - 3),
                assign_at_stack(stack.stack_size - 2, stack.stack_size + 1),
                assign_at_stack(stack.stack_size - 3, stack.stack_size),
            ]);
            stack.stack_size += 2;
        }
        Dup2X2 => {
            if stack.stack_size < 4 {
                return Err(InstructionParseError::StackUnderflow);
            }
            stmts.extend([
                assign_at_stack(stack.stack_size + 1, stack.stack_size - 1),
                assign_at_stack(stack.stack_size, stack.stack_size - 2),
                assign_at_stack(stack.stack_size - 1, stack.stack_size - 3),
                assign_at_stack(stack.stack_size - 2, stack.stack_size - 4),
                assign_at_stack(stack.stack_size - 3, stack.stack_size + 1),
                assign_at_stack(stack.stack_size - 4, stack.stack_size),
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
                return Err(InstructionParseError::StackUnderflow);
            }
            stmts.extend([
                assign(tmp(0), at_stack(stack.stack_size - 1)),
                assign_at_stack(stack.stack_size - 1, stack.stack_size - 2),
                assign(at_stack(stack.stack_size - 2), tmp(0)),
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
        Goto { offset } => stmts.push(jump(one(), *offset as i32)),
        GotoW { offset } => stmts.push(jump(one(), *offset)),
        IfACmpEq { offset } => {
            let rhs = stack.pop()?;
            let lhs = stack.pop()?;
            stmts.push(jump(
                Box::new(Expression::BinOp {
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
                Box::new(Expression::BinOp {
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
                Box::new(Expression::BinOp {
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
                Box::new(Expression::BinOp {
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
                Box::new(Expression::BinOp {
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
                Box::new(Expression::BinOp {
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
                Box::new(Expression::BinOp {
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
                Box::new(Expression::BinOp {
                    lhs,
                    rhs,
                    op: BinOp::Le,
                }),
                *offset as i32,
            ));
        }
        IfEq { offset } => stmts.push(jump(
            Box::new(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: zero(),
                op: BinOp::Eq,
            }),
            *offset as i32,
        )),
        IfNe { offset } => stmts.push(jump(
            Box::new(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: zero(),
                op: BinOp::Ne,
            }),
            *offset as i32,
        )),
        IfLt { offset } => stmts.push(jump(
            Box::new(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: zero(),
                op: BinOp::Lt,
            }),
            *offset as i32,
        )),
        IfGe { offset } => stmts.push(jump(
            Box::new(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: zero(),
                op: BinOp::Ge,
            }),
            *offset as i32,
        )),
        IfGt { offset } => stmts.push(jump(
            Box::new(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: zero(),
                op: BinOp::Gt,
            }),
            *offset as i32,
        )),
        IfLe { offset } => stmts.push(jump(
            Box::new(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: zero(),
                op: BinOp::Le,
            }),
            *offset as i32,
        )),
        IfNonNull { offset } => stmts.push(jump(
            Box::new(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: null(),
                op: BinOp::Ne,
            }),
            *offset as i32,
        )),
        IfNull { offset } => stmts.push(jump(
            Box::new(Expression::BinOp {
                lhs: stack.pop()?,
                rhs: null(),
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
                Box::new(Expression::Call(Call {
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
                &mut stack,
                Index::new(index.as_u16()).unwrap(),
                true,
                true,
            )?);
        }
        InvokeStatic { index } => stmts.push(invoke(&mut stack, *index, false, false)?),
        InvokeInterface { index, .. } => stmts.push(invoke(
            &mut stack,
            Index::new(index.as_u16()).unwrap(),
            true,
            false,
        )?),
        InvokeVirtual { index } => stmts.push(invoke(
            &mut stack,
            Index::new(index.as_u16()).unwrap(),
            true,
            false,
        )?),

        // Field operations
        GetField { index } => {
            let field_ref = pool.retrieve(*index)?;
            let object = stack.pop()?;
            stmts.push(stack.push_nat(&field_ref.name_and_type, field(Some(object), &field_ref)));
        }
        GetStatic { index } => {
            let field_ref = pool.retrieve(*index)?;
            stmts.push(stack.push_nat(&field_ref.name_and_type, field(None, &field_ref)));
        }
        PutField { index } => {
            let field_ref = pool.retrieve(*index)?;
            let value = stack.pop_nat(&field_ref.name_and_type)?;
            let object = stack.pop()?;
            stmts.push(assign(field(Some(object), &field_ref), value));
        }
        PutStatic { index } => {
            let field_ref = pool.retrieve(*index)?;
            let value = stack.pop_nat(&field_ref.name_and_type)?;
            stmts.push(assign(field(None, &field_ref), value));
        }

        // Miscellaneous
        ANewArray { index } => {
            let length = stack.pop()?;
            stmts.push(stack.push(Box::new(Expression::NewArray {
                element_type: Type::Reference(Str(pool.retrieve(*index)?.name)),
                lengths: vec![length],
            })));
        }
        ArrayLength => {
            let array = stack.pop()?;
            stmts.push(stack.push(Box::new(Expression::ArrayLength { array })));
        }
        MultiANewArray { index, dimensions } => {
            let mut lengths: Vec<Box<Expression<'a>>> = (0..*dimensions)
                .map(|_| stack.pop())
                .collect::<Result<_, _>>()?;
            lengths.reverse();
            stmts.push(stack.push(Box::new(Expression::NewArray {
                element_type: Type::Reference(Str(pool.retrieve(*index)?.name)),
                lengths,
            })));
        }
        IInc { index, value } => {
            stmts.push(assign(
                slot(*index as usize),
                Box::new(Expression::BinOp {
                    lhs: slot(*index as usize),
                    rhs: Box::new(Expression::ConstInt(*value as i32)),
                    op: BinOp::Add,
                }),
            ));
        }
        IIncW { index, value } => {
            stmts.push(assign(
                slot(*index as usize),
                Box::new(Expression::BinOp {
                    lhs: slot(*index as usize),
                    rhs: Box::new(Expression::ConstInt(*value as i32)),
                    op: BinOp::Add,
                }),
            ));
        }
        InstanceOf { index } => {
            let object = stack.pop()?;
            stmts.push(stack.push(Box::new(Expression::InstanceOf {
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
            stmts.push(stack.push(Box::new(Expression::NewUninitialized {
                class: Str(pool.retrieve(*index)?.name),
            })));
        }
        NewArray { atype } => {
            let length = stack.pop()?;
            stmts.push(stack.push(Box::new(Expression::NewArray {
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
