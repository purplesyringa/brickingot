use crate::ast::{Arena, DebugIr};
use crate::stackless;
pub use crate::stackless::{ExceptionHandler, Statement};
use core::fmt::{self};

// We reuse the `ExceptionHandler` and `Statement` types from `stackless`, since the only difference
// is whether BB IDs or statement IDs are used. It's a bit janky, but somewhat simplifies things.
#[derive(Debug)]
pub struct Program<'code> {
    pub statements: Vec<Statement>,
    pub exception_handlers: Vec<ExceptionHandler<'code>>,
}

impl<'code> DebugIr<'code> for Program<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        for (stmt_index, stmt) in self.statements.iter().enumerate() {
            writeln!(f, "{stmt_index}: {}", arena.debug(stmt))?;
        }
        for handler in &self.exception_handlers {
            writeln!(f, "{}", arena.debug(handler))?;
        }
        Ok(())
    }
}

pub fn linearize_ir<'code>(mut stackless_ir: stackless::Program<'code>) -> Program<'code> {
    let mut bb_stmt_starts = Vec::new();
    let mut next_stmt_index = 0;
    for bb in &stackless_ir.basic_blocks {
        bb_stmt_starts.push(next_stmt_index);
        next_stmt_index += bb.statements.len();
    }
    bb_stmt_starts.push(next_stmt_index);

    // Fixup jump destinations. We only need to adjust BB terminators.
    for bb in &mut stackless_ir.basic_blocks {
        match bb.statements.last_mut() {
            None | Some(Statement::Basic(_)) => {}
            Some(Statement::Jump { target, .. }) => {
                *target = bb_stmt_starts[*target];
            }
            Some(Statement::Switch { arms, default, .. }) => {
                for (_, target) in arms {
                    *target = bb_stmt_starts[*target];
                }
                *default = bb_stmt_starts[*default];
            }
        }
    }

    // Fixup exception handlers.
    for handler in &mut stackless_ir.exception_handlers {
        // `start` and `end` may compare equal if all basic blocks covered by the `try` block are
        // e.g. `nop`s. But that's not a good reason to remove the handler. Although we know this
        // means `catch` is never executed, removing the exception handler can cause more code to
        // become *syntactically* unreachable, which violates our assumption that all code in the IR
        // is syntactically reachable. Retaining an empty `try` is better than breaking those
        // assumptions.
        handler.active_range.start = bb_stmt_starts[handler.active_range.start];
        handler.active_range.end = bb_stmt_starts[handler.active_range.end];
        handler.body.jump_target = bb_stmt_starts[handler.body.jump_target];
    }

    let mut statements = Vec::with_capacity(next_stmt_index);
    for bb in stackless_ir.basic_blocks {
        statements.extend(bb.statements);
    }

    Program {
        statements,
        exception_handlers: stackless_ir.exception_handlers,
    }
}
