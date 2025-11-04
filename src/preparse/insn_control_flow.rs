use noak::reader::attributes::RawInstruction::{self, *};

pub struct InsnControlFlow {
    pub can_jump_to: Vec<u32>,
    pub can_fallthrough: bool,
}

impl InsnControlFlow {
    pub fn is_normal(&self) -> bool {
        self.can_jump_to.is_empty() && self.can_fallthrough
    }
}

pub fn get_insn_control_flow(
    address: u32,
    insn: &RawInstruction<'_>,
) -> Result<InsnControlFlow, core::num::TryFromIntError> {
    let offset_to_address = |offset: i32| (address as i32 + offset).try_into();

    // This compiles to a jump table with a single entry for normal opcodes -- should be predictable
    // enough.
    Ok(match insn {
        // Exits
        AThrow | AReturn | DReturn | FReturn | IReturn | LReturn | Return => InsnControlFlow {
            can_jump_to: Vec::new(),
            can_fallthrough: false,
        },

        // Jumps
        Goto { offset } => InsnControlFlow {
            can_jump_to: vec![offset_to_address(*offset as i32)?],
            can_fallthrough: false,
        },
        GotoW { offset } => InsnControlFlow {
            can_jump_to: vec![offset_to_address(*offset)?],
            can_fallthrough: false,
        },
        IfACmpEq { offset }
        | IfACmpNe { offset }
        | IfICmpEq { offset }
        | IfICmpNe { offset }
        | IfICmpLt { offset }
        | IfICmpGe { offset }
        | IfICmpGt { offset }
        | IfICmpLe { offset }
        | IfEq { offset }
        | IfNe { offset }
        | IfLt { offset }
        | IfGe { offset }
        | IfGt { offset }
        | IfLe { offset }
        | IfNonNull { offset }
        | IfNull { offset } => InsnControlFlow {
            can_jump_to: vec![offset_to_address(*offset as i32)?],
            can_fallthrough: true,
        },
        LookupSwitch(switch) => InsnControlFlow {
            can_jump_to: core::iter::once(switch.default_offset())
                .chain(switch.pairs().map(|pair| pair.offset()))
                .map(offset_to_address)
                .collect::<Result<Vec<_>, _>>()?,
            can_fallthrough: false,
        },
        TableSwitch(switch) => InsnControlFlow {
            can_jump_to: core::iter::once(switch.default_offset())
                .chain(switch.pairs().map(|pair| pair.offset()))
                .map(offset_to_address)
                .collect::<Result<Vec<_>, _>>()?,
            can_fallthrough: false,
        },

        // Normal operations
        _ => InsnControlFlow {
            can_jump_to: Vec::new(),
            can_fallthrough: true,
        },
    })
}

pub fn can_insn_throw(insn: &RawInstruction<'_>) -> bool {
    // This is a rabbit hole. As per the JVM spec [1], *any* instruction can throw
    // `VirtualMachineError` if the JVM implementation wishes so, the most commonly encountered
    // subclasses of which are `OutOfMemoryError` and `StackOverflowError`. Figures. But
    // unconditionally returning `true` from this function goes against the intent, which is to
    // remove `try` around non-throwing instructions to correctly decompile `try..catch..finally`.
    //
    // So we're doing what seems reasonable rather than correct, i.e. following the behavior of
    // HotSpot. HotSpot only throws `StackOverflowError` in the prologue of a method (i.e. after
    // `invoke`, but before any bytecode instruction) [2], and `OutOfMemoryError` is only considered
    // recoverable when occurring directly due to memory-allocating instructions. [3] This is not
    // guaranteed to apply to other JVMs, but these assumptions seem realistic enough.
    //
    // [1]: https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-6.html#jvms-6.3
    // [2]: https://pangin.pro/posts/stack-overflow-handling
    // [3]: https://t.me/c/2002502458/4129 (for the sake of posterity)
    match insn {
        // Out-of-bounds array indexes or NPE.
        AALoad | AAStore | BALoad | BAStore | CALoad | CAStore | DALoad | DAStore | FALoad
        | FAStore | IALoad | IAStore | LALoad | LAStore | SALoad | SAStore => true,
        // Negative array sizes, invalid type, or OOM.
        ANewArray { .. } | MultiANewArray { .. } | NewArray { .. } => true,
        // Mismatched `monitorenter`/`monitorexit`.
        AReturn | DReturn | FReturn | IReturn | LReturn | Return => true,
        // NPE (and a couple other things for `monitorexit`).
        ArrayLength | MonitorEnter | MonitorExit => true,
        // NPE, invalid type, or a static field.
        GetField { .. } | PutField { .. } => true,
        // By design.
        AThrow => true,
        // Mismatched or invalid type.
        CheckCast { .. } => true,
        // Error during lazy class initialization or invalid type.
        GetStatic { .. } | PutStatic { .. } => true,
        // Invalid type or OOM.
        New { .. } => true,
        // Integer division by zero.
        IDiv | IRem | LDiv | LRem => true,
        // Propagated from the invoked method, plus stack overflow, among other reasons.
        InvokeDynamic { .. }
        | InvokeInterface { .. }
        | InvokeSpecial { .. }
        | InvokeStatic { .. }
        | InvokeVirtual { .. } => true,
        // Invalid type.
        InstanceOf { .. } | LdC { .. } | LdCW { .. } | LdC2W { .. } => true,
        // Covers constants, loads/stores to slots, stack manipulation, primitive type conversion,
        // arithmetic, comparisons, and jumps. Too long to actually list here, sorry.
        _ => false,
    }
}
