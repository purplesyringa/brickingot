use crate::arena::{Arena, DebugIr, ExprId};
use crate::ast::{BasicStatement, Expression, Str, VariableNamespace};
use crate::insn_ir_import::{import_insn_to_ir, InsnIrImportError};
use crate::preparse;
use crate::stack_machine::StackMachine;
use std::collections::HashMap;
// use crate::insn2stmt::{convert_instruction_to_unstructured_ast, InstructionParseError};
// use crate::instructions::{
//     get_instruction_stack_adjustment, get_instruction_successors, InstructionPreParseError,
// };

use core::fmt::{self, Display};
use noak::{
    error::DecodeError,
    reader::{
        attributes::{Code, Index},
        cpool::ConstantPool,
    },
    MStr,
};
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

pub fn build_stackless_ir<'code>(
    arena: &Arena<'code>,
    pool: &ConstantPool<'code>,
    code: &Code<'code>,
    basic_blocks: Vec<preparse::BasicBlock>,
) -> Result<Program<'code>, StacklessIrError> {
    let mut statements = Vec::new();

    // Iterate over BB instruction ranges instead of the whole code, as dead BBs may contain invalid
    // bytecode and we'd rather not worry about that.
    for bb in &basic_blocks {
        let mut stack = StackMachine {
            arena,
            stack_size: bb.stack_size_at_start,
        };
        let stmt_range_start = statements.len();

        for row in code.raw_instructions_from(Index::new(bb.instruction_range.start))? {
            let (address, insn) = row?;
            let address = address.as_u32();
            if address >= bb.instruction_range.end {
                assert_eq!(address, bb.instruction_range.end);
                break;
            }

            let stack_size_before_insn = stack.stack_size;
            // Jump targets are initialized to instruction addresses. We'll remap them to statement
            // indices after all instructions have been converted.
            import_insn_to_ir(&mut stack, pool, address, &insn, &mut statements).map_err(
                |error| StacklessIrError::InsnIrImport {
                    address,
                    insn: format!("{insn:?}"),
                    stack_size_before_insn,
                    error,
                },
            )?;
        }

        // Certain variables we create can correspond to multiple source-level variables. This
        // includes both stack variables, which can correspond to several independent expressions,
        // and slots, which can correspond to variables local to distinct non-nested blocks. We want
        // to split such variables into many.
        //
        // This is kind of similar to SSA: we could convert the IR to SSA and then merge all related
        // variables, i.e. those mentioned by live phi functions, together. That's not the best way,
        // because computing SSA fast requires complicated algorithms, and we don't really need SSA
        // in any intermediate IR -- all we want is to be able to inline single definitions into
        // single uses, and we don't need SSA for that.
        //
        // For each variable use, we want to determine which definitions the variable value could
        // come from. We'll get to handling cross-BB references in a moment, but for now, let's
        // handle individual BBs.
        let mut active_defs: HashMap<(usize, VariableNamespace), usize> = HashMap::new();
        for (stmt_id, stmt) in statements.iter().enumerate().skip(stmt_range_start) {
            if let Statement::Basic(BasicStatement::Assign { target, .. }) = stmt
                && let Expression::Variable { id, namespace } = arena[*target]
            {
                active_defs.insert((id, namespace), stmt_id);
            }
        }
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
        statements,
        exception_handlers,
    })
}
