use crate::ast::{BasicStatement, Expression, Str};
use crate::insn2stmt::{InstructionParseError, convert_instruction_to_unstructured_ast};
use crate::instructions::{
    InstructionPreParseError, get_instruction_stack_adjustment, get_instruction_successors,
};

use core::fmt::{self, Display};
use displaydoc::Display;
use noak::{
    MStr,
    error::DecodeError,
    reader::{
        attributes::{Code, RawInstruction},
        cpool::ConstantPool,
    },
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum StatementGenerationError {
    #[error("Failed to parse class file: {0}")]
    Noak(#[from] DecodeError),

    #[error("While pre-parsing instruction `{insn}`: {error}")]
    InstructionPreParse {
        insn: String,
        error: InstructionPreParseError,
    },

    #[error("While parsing instruction `{insn}`: {error}")]
    InstructionParse {
        insn: String,
        error: InstructionParseError,
    },

    #[error(
        "Jump to address {0} jumps into the middle of an instruction (or after the last instruction)"
    )]
    IllegalJump(u32),

    #[error(
        "Exception handler at address {0} is the middle of an instruction (or after the last instruction)"
    )]
    IllegalExceptionHandler(u32),

    #[error("Execution reaches the end of bytecode")]
    CodeFallthrough,

    #[error("Found execution paths that reach a single address at different stack heights")]
    InconsistentStackSize,
}

#[derive(Debug, Display)]
pub struct Program<'a> {
    pub statements: Vec<Statement<'a>>,
    pub exception_handlers: Vec<ExceptionHandler<'a>>,
}

impl Display for Program<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, stmt) in self.statements.iter().enumerate() {
            write!(f, "{i}: {stmt}\n")?;
        }
        for handler in &self.exception_handlers {
            write!(f, "{handler}\n")?;
        }
        Ok(())
    }
}

#[derive(Debug, Display)]
pub enum Statement<'a> {
    /// {0}
    Basic(BasicStatement<'a>),
    /// if ({condition}) jump {target};
    Jump {
        condition: JumpCondition<'a>,
        target: usize,
    },
    /// {0}
    Switch(Switch<'a>),
}

#[derive(Debug)]
pub struct Switch<'a> {
    pub key: Box<Expression<'a>>,
    pub successors: Vec<(i32, usize)>,
    pub default: usize,
}

impl Display for Switch<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "switch ({}) ", self.key)?;
        for (value, successor) in &self.successors {
            write!(f, "{value} => jump {successor}; ")?;
        }
        write!(f, "default => jump {};", self.default)
    }
}

#[derive(Debug)]
pub struct ExceptionHandler<'a> {
    pub start: usize,
    pub end: usize,
    pub target: usize,
    pub class: Option<Str<'a>>,
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

#[derive(Debug, Display)]
pub enum JumpCondition<'a> {
    /// true
    Always,
    /// ({0}) == ({1})
    Eq(Box<Expression<'a>>, Box<Expression<'a>>),
    /// ({0}) != ({1})
    Ne(Box<Expression<'a>>, Box<Expression<'a>>),
    /// ({0}) >= ({1})
    Ge(Box<Expression<'a>>, Box<Expression<'a>>),
    /// ({0}) > ({1})
    Gt(Box<Expression<'a>>, Box<Expression<'a>>),
    /// ({0}) <= ({1})
    Le(Box<Expression<'a>>, Box<Expression<'a>>),
    /// ({0}) < ({1})
    Lt(Box<Expression<'a>>, Box<Expression<'a>>),
}

pub fn convert_code_to_stackless<'a>(
    pool: &ConstantPool<'a>,
    code: &Code<'a>,
) -> Result<Program<'a>, StatementGenerationError> {
    // The result of this pass is a series of "high-level" instructions with unstructured control
    // flow, represented in an AST of a similar kind to the one we emit. Such an AST does not
    // introduce basic blocks, so we don't try to do this here either to just throw it away
    // immediately. This pass should be fast enough for a small win from BBs to not matter
    // significantly, if at all.

    // We don't try to topsort the instructions because javac should have produced code in
    // a "good enough" order anyway (and we don't rely on the instruction order for correctness,
    // only for decompilation quality). In fact, chances are, javac order closely mirrors the
    // original program, and our attempts would produce code further from the source.

    // noak does not provide an API to parse an instruction at address, and building a CFG requires
    // random access, so we have to pre-parse the instructions into an array. `instructions` is
    // indexed by the instruction address, not by its index in the list.
    let mut instructions: Vec<Option<(RawInstruction<'_>, u32)>> = Vec::new();
    let mut raw_instructions = code.raw_instructions().peekable();
    while let Some(row) = raw_instructions.next() {
        let (address, insn) = row?;
        let address = address.as_u32();
        // println!("{address:?} {insn:?}");
        let next_address = match raw_instructions.peek() {
            Some(next_row) => next_row.as_ref().map_err(|e| e.clone())?.0.as_u32(),
            None => u32::MAX,
        };
        instructions.resize_with(address as usize + 1, || None);
        instructions[address as usize] = Some((insn, next_address));
    }

    if instructions.is_empty() {
        return Err(StatementGenerationError::CodeFallthrough);
    }

    // Compute stack sizes *prior to* each instruction.
    let mut stack_sizes = vec![None; instructions.len()];
    stack_sizes[0] = Some(0);

    let mut dfs_stack = vec![0];
    for handler in code.exception_handlers() {
        let address = handler.handler().as_u32();
        let Some(Some(_)) = instructions.get(address as usize) else {
            return Err(StatementGenerationError::IllegalExceptionHandler(address));
        };
        // Don't attempt to insert a single address into the stack several times.
        if stack_sizes[address as usize].replace(1).is_none() {
            dfs_stack.push(address);
        }
    }

    // Precondition: every address in `dfs_stack` is less than `instructions.len()`.
    while let Some(address) = dfs_stack.pop() {
        let (insn, next_address) = instructions[address as usize]
            .as_ref()
            .ok_or(StatementGenerationError::IllegalJump(address))?;

        let (stack_adjustment, successors) = (|| {
            Ok((
                get_instruction_stack_adjustment(pool, insn)?,
                get_instruction_successors(address, *next_address, insn)?,
            ))
        })()
        .map_err(|error| StatementGenerationError::InstructionPreParse {
            insn: format!("{insn:?}"),
            error,
        })?;

        let stack_size = stack_sizes[address as usize].unwrap();
        let next_stack_size = stack_size + stack_adjustment;

        for successor_address in successors {
            if successor_address as usize >= instructions.len() {
                return Err(StatementGenerationError::IllegalJump(successor_address));
            }
            if let Some(expected_next_stack_size) = stack_sizes[successor_address as usize] {
                if next_stack_size != expected_next_stack_size {
                    return Err(StatementGenerationError::InconsistentStackSize);
                }
            } else {
                stack_sizes[successor_address as usize] = Some(next_stack_size);
                dfs_stack.push(successor_address);
            }
        }
    }

    // Transform instructions to the AST form. We couldn't do that during DFS because we need to
    // retain the order, and we couldn't fill an array because some opcodes map to multiple AST
    // statements.
    //
    // Jump targets are initialized to *instruction addresses* and then remapped to statement
    // indices after all instructions have been converted.
    let mut statements = Vec::new();
    let mut insn_to_statement_index = vec![usize::MAX; instructions.len()];
    for (address, insn) in instructions.iter().enumerate() {
        let Some((insn, _)) = insn else {
            continue;
        };

        let Some(stack_size) = stack_sizes[address] else {
            // Unreachable instruction, can be safely ignored.
            continue;
        };

        insn_to_statement_index[address] = statements.len();

        (|| {
            convert_instruction_to_unstructured_ast(
                pool,
                address as u32,
                stack_size
                    .try_into()
                    .map_err(|_| InstructionParseError::StackUnderflow)?,
                &insn,
                &mut statements,
            )
        })()
        .map_err(|error| StatementGenerationError::InstructionParse {
            insn: format!("{insn:?}"),
            error,
        })?;
    }

    // Fixup jump destinations
    for stmt in &mut statements {
        match stmt {
            Statement::Basic(_) => {}
            Statement::Jump { target, .. } => *target = insn_to_statement_index[*target],
            Statement::Switch(Switch {
                successors,
                default,
                ..
            }) => {
                for (_, successor) in successors {
                    *successor = insn_to_statement_index[*successor];
                }
                *default = insn_to_statement_index[*default];
            }
        }
    }

    // Compute new exception handlers
    let mut exception_handlers = Vec::new();
    for handler in code.exception_handlers() {
        let start = insn_to_statement_index
            .get(handler.start().as_u32() as usize)
            .copied()
            .unwrap_or(statements.len());
        let end = insn_to_statement_index
            .get(handler.end().as_u32() as usize)
            .copied()
            .unwrap_or(statements.len());
        let target = insn_to_statement_index[handler.handler().as_u32() as usize];
        let class = match handler.catch_type() {
            Some(catch_type) => Some(Str(pool.retrieve(catch_type)?.name)),
            None => None,
        };
        exception_handlers.push(ExceptionHandler {
            start,
            end,
            target,
            class,
        });
    }

    Ok(Program {
        statements,
        exception_handlers,
    })
}
