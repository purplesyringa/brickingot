use crate::abstract_eval::Machine;
use crate::arena::{Arena, DebugIr, ExprId};
use crate::ast::{BasicStatement, Expression, Str, VariableName};
use crate::insn_ir_import::{import_insn_to_ir, InsnIrImportError};
use crate::insn_stack_effect::is_type_descriptor_double_width;
use crate::preparse;
use core::fmt::{self, Display};
use noak::{
    descriptor::MethodDescriptor,
    error::DecodeError,
    reader::{
        attributes::{Code, Index},
        cpool::ConstantPool,
    },
    MStr,
};
use rustc_hash::FxHashMap;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum StacklessIrError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("While importing instruction `{address}: {insn}` to IR: {error} (stack size before instruction was {stack_size_before_insn})")]
    InsnIrImport {
        address: u32,
        insn: String,
        stack_size_before_insn: usize,
        error: InsnIrImportError,
    },
}

#[derive(Debug)]
pub struct Program<'code> {
    pub statements: Vec<Statement>,
    pub exception_handlers: Vec<ExceptionHandler<'code>>,
}

impl<'code> DebugIr<'code> for Program<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        for (i, stmt) in self.statements.iter().enumerate() {
            write!(f, "{i}: {}\n", arena.debug(stmt))?;
        }
        for handler in &self.exception_handlers {
            write!(f, "{handler}\n")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum Statement {
    Basic(BasicStatement),
    Jump {
        condition: ExprId,
        target: usize,
    },
    Switch {
        key: ExprId,
        arms: Vec<(i32, usize)>,
        default: usize,
    },
}

impl<'code> DebugIr<'code> for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        match self {
            Self::Basic(stmt) => write!(f, "{}", arena.debug(stmt)),
            Self::Jump { condition, target } => {
                write!(f, "if ({}) jump {target};", arena.debug(condition))
            }
            Self::Switch { key, arms, default } => {
                write!(f, "switch ({}) ", arena.debug(key))?;
                for (value, target) in arms {
                    write!(f, "{value} => jump {target}; ")?;
                }
                write!(f, "default => jump {default};")
            }
        }
    }
}

#[derive(Debug)]
pub struct ExceptionHandler<'code> {
    pub start: usize,
    pub end: usize,
    pub target: usize,
    pub class: Option<Str<'code>>,
}

impl Display for ExceptionHandler<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "try {{ {}..{} }} catch ({}) {{ goto {}; }}",
            self.start,
            self.end,
            self.class
                .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
            self.target,
        )
    }
}

#[derive(Clone)]
struct BasicBlock {
    active_defs_at_end: FxHashMap<VariableName, ExprId>,
    predecessors: Vec<usize>,
}

impl BasicBlock {
    fn new() -> Self {
        Self {
            active_defs_at_end: FxHashMap::default(),
            predecessors: Vec::new(),
        }
    }
}

pub fn build_stackless_ir<'code>(
    arena: &Arena<'code>,
    pool: &ConstantPool<'code>,
    code: &Code<'code>,
    method_descriptor: &MethodDescriptor<'code>,
    is_static: bool,
    preparse_basic_blocks: Vec<preparse::BasicBlock>,
) -> Result<Program<'code>, StacklessIrError> {
    let mut machine = Machine {
        arena,
        stack_size: 0,
        active_defs: FxHashMap::default(),
        unresolved_uses: FxHashMap::default(),
        bb_id: usize::MAX,
        statements: Vec::new(),
    };

    let mut next_slot_id = 0;
    if !is_static {
        machine.set_slot(next_slot_id, arena.alloc(Expression::This));
        next_slot_id += 1;
    }
    for (index, ty) in method_descriptor.parameters().enumerate() {
        let value = arena.alloc(Expression::Argument { index });
        machine.set_slot(next_slot_id, value);
        next_slot_id += if is_type_descriptor_double_width(&ty) {
            2
        } else {
            1
        };
    }

    let mut ir_basic_blocks = vec![BasicBlock::new(); preparse_basic_blocks.len()];

    // Iterate over BB instruction ranges instead of the whole code, as dead BBs may contain invalid
    // bytecode and we'd rather not worry about that.
    for (bb_id, bb) in preparse_basic_blocks.iter().enumerate() {
        machine.stack_size = bb.stack_size_at_start;
        machine.bb_id = bb_id;

        for succ_bb_id in &bb.successors {
            ir_basic_blocks[*succ_bb_id].predecessors.push(bb_id);
        }

        for row in code.raw_instructions_from(Index::new(bb.instruction_range.start))? {
            let (address, insn) = row?;
            let address = address.as_u32();
            if address >= bb.instruction_range.end {
                assert_eq!(address, bb.instruction_range.end);
                break;
            }

            let stack_size_before_insn = machine.stack_size;
            // Jump targets are initialized to instruction addresses. We'll remap them to statement
            // indices after all instructions have been converted.
            import_insn_to_ir(&mut machine, pool, address, &insn).map_err(|error| {
                StacklessIrError::InsnIrImport {
                    address,
                    insn: format!("{insn:?}"),
                    stack_size_before_insn,
                    error,
                }
            })?;
        }

        ir_basic_blocks[bb_id].active_defs_at_end = machine
            .active_defs
            .drain()
            .filter(|(_, def)| !def.is_fake)
            .map(|(var, def)| (var, def.version))
            .collect();
    }

    // Certain variables we create can correspond to multiple source-level variables. This includes
    // both stack variables, which can correspond to several independent expressions, and slots,
    // which can correspond to variables local to distinct non-nested blocks. We want to split such
    // variables into many independent ones.
    //
    // This is kind of similar to SSA: we could, for example, convert the IR to SSA and then merge
    // all related variables, i.e. those mentioned by live phi functions, together. That's not the
    // best way, because computing SSA fast requires complicated algorithms, and we don't really
    // need SSA in any intermediate IR -- all we want is to be able to inline single definitions
    // into single uses, and we don't need SSA for that.
    //
    // The main thing we lose from avoiding SSA is the ability to merge `x` and `y` into one
    // variable upon encountering `x = y`. There's two problems with this:
    //
    // - Even if `x` is single-def, replacing `x` with `y` at each use could cause the wrong version
    //   of `y` to be accessed if `y` is reassigned between `x = y` and use of `x`. This can be
    //   avoided by refusing to merge variables in this case, but...
    // - If, after the assignment `slotN = stackM`, `stackM` is accessed again, e.g. as in
    //   `f(a = x)`, `stackM` would be saved into a separate variable. This can be fixed by changing
    //   the definition of `stackM` to the return value of the assignment operator. However, if
    //   `stackM` is itself defined by `stackM = stackK`, we'd also need to reassign `stackK`, and
    //   this could span across BBs and quickly becomes messy.
    //
    // I'm not sure what to do about this...
    //
    // In a nutshell, for each variable use, we want to determine which definitions its value could
    // come from, and request that those definition share a variable. The components of such
    // a DSU-like structure then correspond to individual variables.
    //
    // We've already linked uses to definitions within basic blocks. We now need to link unresolved
    // uses to non-fake active definitions in predecessors. There's a relatively simple way to
    // achieve this per-variable with DFS. The total time complexity becomes
    // O(n_variables * n_basic_blocks), which sucks, because most other algorithms we use are
    // quasi-linear, but SSA-adjacent stuff can't really be any faster.
    for (name, uses) in machine.unresolved_uses {
        if ir_basic_blocks.len() == 1 {
            println!("woah {name}");
        }
        //     for (bb_id, use_expr_id) in uses {}
    }

    // // Fixup jump destinations
    // for stmt in &mut statements {
    //     match stmt {
    //         Statement::Basic(_) => {}
    //         Statement::Jump { target, .. } => *target = insn_to_statement_index[*target],
    //         Statement::Switch(Switch { arms, default, .. }) => {
    //             for (_, target) in arms {
    //                 *target = insn_to_statement_index[*target];
    //             }
    //             *default = insn_to_statement_index[*default];
    //         }
    //     }
    // }

    // // Compute new exception handlers
    let mut exception_handlers = Vec::new();
    // for handler in code.exception_handlers() {
    //     let start = insn_to_statement_index
    //         .get(handler.start().as_u32() as usize)
    //         .copied()
    //         .unwrap_or(statements.len());
    //     let end = insn_to_statement_index
    //         .get(handler.end().as_u32() as usize)
    //         .copied()
    //         .unwrap_or(statements.len());
    //     let target = insn_to_statement_index[handler.handler().as_u32() as usize];
    //     let class = match handler.catch_type() {
    //         Some(catch_type) => Some(Str(pool.retrieve(catch_type)?.name)),
    //         None => None,
    //     };
    //     exception_handlers.push(ExceptionHandler {
    //         start,
    //         end,
    //         target,
    //         class,
    //     });
    // }

    Ok(Program {
        statements: machine.statements,
        exception_handlers,
    })
}
