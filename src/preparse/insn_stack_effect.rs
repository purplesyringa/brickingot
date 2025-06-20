use noak::{
    descriptor::{BaseType, MethodDescriptor, TypeDescriptor},
    error::DecodeError,
    reader::{
        attributes::RawInstruction::{self, *},
        cpool::{value::NameAndType, ConstantPool, InterfaceMethodRef, Item, MethodRef},
    },
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum InsnStackEffectError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("The legacy JSR instruction is unsupported")]
    JsrUnsupported,

    #[error(
        "Expected a MethodRef or an InterfaceMethodRef, found a different type in constant pool"
    )]
    NotAMethodRef,
}

pub fn get_insn_stack_effect(
    pool: &ConstantPool<'_>,
    insn: &RawInstruction<'_>,
) -> Result<isize, InsnStackEffectError> {
    // This could be resolve via a table in most cases. LLVM compiles this as a jump table instead,
    // which is not ideal, but fine. No need to optimize this, at least for now.
    Ok(match insn {
        // Array loads/stores
        AALoad | BALoad | CALoad | FALoad | IALoad | SALoad => -1,
        DALoad | LALoad => 0,
        AAStore | BAStore | CAStore | FAStore | IAStore | SAStore => -3,
        DAStore | LAStore => -4,

        // Slot load/stores
        ALoad { .. }
        | ALoadW { .. }
        | ALoad0
        | ALoad1
        | ALoad2
        | ALoad3
        | FLoad { .. }
        | FLoadW { .. }
        | FLoad0
        | FLoad1
        | FLoad2
        | FLoad3
        | ILoad { .. }
        | ILoadW { .. }
        | ILoad0
        | ILoad1
        | ILoad2
        | ILoad3 => 1,
        DLoad { .. }
        | DLoadW { .. }
        | DLoad0
        | DLoad1
        | DLoad2
        | DLoad3
        | LLoad { .. }
        | LLoadW { .. }
        | LLoad0
        | LLoad1
        | LLoad2
        | LLoad3 => 2,
        AStore { .. }
        | AStoreW { .. }
        | AStore0
        | AStore1
        | AStore2
        | AStore3
        | FStore { .. }
        | FStoreW { .. }
        | FStore0
        | FStore1
        | FStore2
        | FStore3
        | IStore { .. }
        | IStoreW { .. }
        | IStore0
        | IStore1
        | IStore2
        | IStore3 => -1,
        DStore { .. }
        | DStoreW { .. }
        | DStore0
        | DStore1
        | DStore2
        | DStore3
        | LStore { .. }
        | LStoreW { .. }
        | LStore0
        | LStore1
        | LStore2
        | LStore3 => -2,

        // Constants
        AConstNull
        | BIPush { .. }
        | SIPush { .. }
        | FConst0
        | FConst1
        | FConst2
        | IConstM1
        | IConst0
        | IConst1
        | IConst2
        | IConst3
        | IConst4
        | IConst5
        | LdC { .. }
        | LdCW { .. } => 1,
        DConst0 | DConst1 | LConst0 | LConst1 | LdC2W { .. } => 2,

        // Conversions
        CheckCast { .. } => 0,
        D2L | F2I | I2B | I2C | I2F | I2S | L2D => 0,
        D2F | D2I | L2F | L2I => -1,
        F2D | F2L | I2D | I2L => 1,

        // Arithmetic
        DAdd | DSub | DMul | DDiv | DRem | LAdd | LSub | LMul | LDiv | LRem => -2,
        IAdd | ISub | IMul | IDiv | IRem | FAdd | FSub | FMul | FDiv | FRem => -1,
        LAnd | LOr | LXor => -2,
        LShL | LShR | LUShR => -1,
        IAnd | IOr | IShL | IShR | IUShR | IXor => -1,
        DCmpG | DCmpL | LCmp => -3,
        FCmpG | FCmpL => -1,
        DNeg | FNeg | INeg | LNeg => 0,

        // Stack manipulation
        Dup | DupX1 | DupX2 => 1,
        Dup2 | Dup2X1 | Dup2X2 => 2,
        Pop => -1,
        Pop2 => -2,
        Swap => 0,

        // Exits. These have no successors, so the adjustment doesn't matter.
        AThrow | AReturn | DReturn | FReturn | IReturn | LReturn | Return => 0,

        // Jumps
        Goto { .. } | GotoW { .. } => 0,
        IfACmpEq { .. }
        | IfACmpNe { .. }
        | IfICmpEq { .. }
        | IfICmpNe { .. }
        | IfICmpLt { .. }
        | IfICmpGe { .. }
        | IfICmpGt { .. }
        | IfICmpLe { .. } => -2,
        IfEq { .. }
        | IfNe { .. }
        | IfLt { .. }
        | IfGe { .. }
        | IfGt { .. }
        | IfLe { .. }
        | IfNonNull { .. }
        | IfNull { .. }
        | LookupSwitch(_)
        | TableSwitch(_) => -1,

        // Function calls
        InvokeDynamic { index } => get_method_stack_effect(&pool.retrieve(*index)?.name_and_type)?,
        InvokeInterface { index, .. } => {
            get_method_stack_effect(&pool.retrieve(*index)?.name_and_type)? - 1
        }
        InvokeSpecial { index } => {
            let name_and_type = match pool.get(*index)? {
                Item::MethodRef(MethodRef { name_and_type, .. }) => name_and_type,
                Item::InterfaceMethodRef(InterfaceMethodRef { name_and_type, .. }) => name_and_type,
                _ => return Err(InsnStackEffectError::NotAMethodRef),
            };
            get_method_stack_effect(&pool.retrieve(*name_and_type)?)? - 1
        }
        InvokeStatic { index } => {
            let name_and_type = match pool.get(*index)? {
                Item::MethodRef(MethodRef { name_and_type, .. }) => name_and_type,
                Item::InterfaceMethodRef(InterfaceMethodRef { name_and_type, .. }) => name_and_type,
                _ => return Err(InsnStackEffectError::NotAMethodRef),
            };
            get_method_stack_effect(&pool.retrieve(*name_and_type)?)?
        }
        InvokeVirtual { index } => {
            get_method_stack_effect(&pool.retrieve(*index)?.name_and_type)? - 1
        }

        // Field operations
        GetField { index } => {
            if is_name_and_type_double_width(&pool.retrieve(*index)?.name_and_type) {
                1
            } else {
                0
            }
        }
        GetStatic { index } => {
            if is_name_and_type_double_width(&pool.retrieve(*index)?.name_and_type) {
                2
            } else {
                1
            }
        }
        PutField { index } => {
            if is_name_and_type_double_width(&pool.retrieve(*index)?.name_and_type) {
                -3
            } else {
                -2
            }
        }
        PutStatic { index } => {
            if is_name_and_type_double_width(&pool.retrieve(*index)?.name_and_type) {
                -2
            } else {
                -1
            }
        }

        // Miscellaneous
        ANewArray { .. } | ArrayLength => 0,
        MultiANewArray { dimensions, .. } => 1 - *dimensions as isize,
        IInc { .. } | IIncW { .. } => 0,
        InstanceOf { .. } => 0,
        JSr { .. } | JSrW { .. } | Ret { .. } | RetW { .. } => {
            return Err(InsnStackEffectError::JsrUnsupported);
        }
        MonitorEnter | MonitorExit => -1,
        New { .. } => 1,
        NewArray { .. } => 0,
        Nop => 0,
    })
}

fn get_method_stack_effect(name_and_type: &NameAndType<'_>) -> Result<isize, InsnStackEffectError> {
    // For the return type in particular, we could check whether the method descriptor ends
    // with `)V`, `)D`, `)J`, or anything else. But we also have to check argument
    // categories, which cannot be computed that easily without parsing, so let's bite the bullet.
    // XXX: This is quite slow. Can we improve performance here?
    let method_descriptor = MethodDescriptor::parse(name_and_type.descriptor)?;

    let arguments_size: isize = method_descriptor
        .parameters()
        .map(|param| {
            if is_type_descriptor_double_width(&param) {
                2
            } else {
                1
            }
        })
        .sum();

    let return_size = if let Some(ret) = method_descriptor.return_type() {
        if is_type_descriptor_double_width(&ret) {
            2
        } else {
            1
        }
    } else {
        0
    };

    Ok(return_size - arguments_size)
}

// Checks if a field descriptor is of type `double` or `long`.
pub fn is_name_and_type_double_width(name_and_type: &NameAndType<'_>) -> bool {
    // D is double, J is long
    name_and_type.descriptor == "D" || name_and_type.descriptor == "J"
}

pub fn is_type_descriptor_double_width(descriptor: &TypeDescriptor<'_>) -> bool {
    descriptor.dimensions == 0 && matches!(descriptor.base, BaseType::Double | BaseType::Long)
}
