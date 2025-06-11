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
