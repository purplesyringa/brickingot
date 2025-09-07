use super::solver::{
    Node, RequirementImplementation, RequirementKey, compute_block_requirements,
    satisfy_block_requirements,
};
use super::{Catch, Statement};
use crate::arena::{Arena, ExprId};
use crate::ast::{BasicStatement, Expression, Variable, VariableName, VariableNamespace};
use crate::stackless;
use rustc_hash::FxHashMap;

pub fn structure_control_flow<'code>(
    arena: &Arena<'code>,
    stackless_ir: stackless::Program<'code>,
) -> Vec<Statement<'code>> {
    let (requirements, mut keys) = compute_block_requirements(&stackless_ir);
    let (tree, implementations, next_block_id) =
        satisfy_block_requirements(stackless_ir.statements.len(), requirements);

    // Add keys for dynamically created dispatch jumps.
    let mut id = keys.len();
    keys.resize_with(implementations.len(), || {
        let key = RequirementKey::Dispatch { id };
        id += 1;
        key
    });

    let mut try_block_to_handlers: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    let mut jump_implementations = FxHashMap::default();
    let mut has_dispatch = false;
    for (key, imp) in keys.into_iter().zip(implementations) {
        if let RequirementImplementation::Try { block_id } = imp {
            let RequirementKey::Try { index } = key else {
                panic!("unexpected key for try implementation");
            };
            try_block_to_handlers
                .entry(block_id)
                .or_default()
                .push(index);
        } else {
            if let RequirementKey::Dispatch { .. } = key {
                has_dispatch = true;
            }
            jump_implementations.insert(key, imp);
        }
    }

    let mut structurizer = Structurizer {
        arena,
        stackless_ir,
        try_block_to_handlers,
        jump_implementations,
        next_block_id,
        unique_selector_id: arena.alloc(Expression::Null), // doesn't matter, just a unique ID
    };

    let mut stmts = Vec::new();
    if has_dispatch {
        stmts.push(Statement::Basic {
            index: None,
            stmt: BasicStatement::Assign {
                target: structurizer.selector(),
                value: arena.int(0),
            },
        });
    }
    for node in tree {
        structurizer.emit_node(node, &mut stmts);
    }

    stmts
}

struct Structurizer<'arena, 'code> {
    arena: &'arena Arena<'code>,
    stackless_ir: stackless::Program<'code>,
    try_block_to_handlers: FxHashMap<usize, Vec<usize>>,
    jump_implementations: FxHashMap<RequirementKey, RequirementImplementation>,
    next_block_id: usize,
    unique_selector_id: ExprId,
}

impl<'code> Structurizer<'_, 'code> {
    fn emit_tree(&mut self, tree: Vec<Node>) -> Vec<Statement<'code>> {
        let mut stmts = Vec::with_capacity(tree.len()); // underestimating, but better than nothing
        for node in tree {
            self.emit_node(node, &mut stmts);
        }
        stmts
    }

    fn emit_node(&mut self, node: Node, out: &mut Vec<Statement<'code>>) {
        match node {
            Node::Linear { stmt_range } => {
                for stmt_index in stmt_range {
                    self.emit_stmt(stmt_index, out);
                }
            }

            Node::Block { id, children } => out.push(Statement::Block {
                id,
                children: self.emit_tree(children),
            }),

            Node::Try { id, children } => out.push(Statement::Try {
                children: self.emit_tree(children),
                catches: self
                    .try_block_to_handlers
                    .remove(&id)
                    .expect("try block without catches")
                    .into_iter()
                    .map(|handler| {
                        let key = RequirementKey::BackwardCatch { index: handler };
                        let handler = self.stackless_ir.exception_handlers[handler].clone();

                        let mut children = Vec::new();
                        if let Some((stack0_version, exception0_version)) =
                            handler.stack0_exception0_copy_versions
                        {
                            children.push(Statement::Basic {
                                index: None,
                                stmt: BasicStatement::Assign {
                                    target: self.arena.alloc(Expression::Variable(Variable {
                                        name: VariableName {
                                            id: 0,
                                            namespace: VariableNamespace::Stack,
                                        },
                                        version: stack0_version,
                                    })),
                                    value: self.arena.alloc(Expression::Variable(Variable {
                                        name: VariableName {
                                            id: 0,
                                            namespace: VariableNamespace::Exception,
                                        },
                                        version: exception0_version,
                                    })),
                                },
                            });
                        }
                        if self.jump_implementations.contains_key(&key) {
                            self.emit_jump(key, &mut children);
                        }

                        Catch {
                            class: handler.class,
                            children,
                            active_range: handler.start..handler.end,
                        }
                    })
                    .collect(),
            }),

            Node::DispatchSwitch { dispatch_targets } => {
                // Dispatch targets can never point to the statement after the switch, since such
                // jumps would be trivially lowered to a normal, non-dispatch jump to this `switch`.
                let id = self.next_block_id;
                self.next_block_id += 1;
                out.push(Statement::Switch {
                    id,
                    key: self.selector(),
                    arms: dispatch_targets
                        .into_iter()
                        .map(|target| {
                            let mut stmts = vec![Statement::Basic {
                                index: None,
                                stmt: BasicStatement::Assign {
                                    target: self.selector(),
                                    value: self.arena.int(0),
                                },
                            }];
                            self.emit_jump(
                                RequirementKey::Dispatch {
                                    id: target.jump_req_id,
                                },
                                &mut stmts,
                            );
                            (Some(target.selector), stmts)
                        })
                        .collect(),
                });
            }
        }
    }

    fn emit_stmt(&mut self, stmt_index: usize, out: &mut Vec<Statement<'code>>) {
        // Need to replace with *something*, `return;` works fine.
        let stmt = core::mem::replace(
            &mut self.stackless_ir.statements[stmt_index],
            stackless::Statement::Basic(BasicStatement::ReturnVoid),
        );

        match stmt {
            stackless::Statement::Basic(stmt) => out.push(Statement::Basic {
                index: Some(stmt_index),
                stmt,
            }),

            stackless::Statement::Label { .. } => {
                unreachable!("labels should've been removed on the previous pass")
            }

            stackless::Statement::Jump { condition, .. } => {
                let out = if let Expression::ConstInt(1) = self.arena[condition] {
                    out
                } else {
                    out.push(Statement::If {
                        condition,
                        then_children: Vec::new(),
                    });
                    let Some(Statement::If { then_children, .. }) = out.last_mut() else {
                        unreachable!()
                    };
                    then_children
                };
                self.emit_jump(RequirementKey::Jump { stmt_index }, out);
            }

            stackless::Statement::Switch { key, arms, default } => {
                // Switches are only guaranteed to have a quality lowering if the arms are sorted by
                // target.
                let mut arms: Vec<(Option<i32>, usize)> = core::iter::once((None, default))
                    .chain(arms.iter().map(|(key, target)| (Some(*key), *target)))
                    .collect();
                arms.sort_unstable_by_key(|(_, target)| *target);

                let id = self.next_block_id;
                self.next_block_id += 1;
                out.push(Statement::Switch {
                    id,
                    key,
                    arms: arms
                        .iter()
                        .enumerate()
                        .map(|(i, &(key, target))| {
                            let mut children = Vec::new();
                            if let Some((_, next_target)) = arms.get(i + 1)
                                && target == *next_target
                            {
                                // Allow arms to the same target to fallthrough, so that we get
                                // a nice `case 1: case 2: ... case n:` decompilation.
                                // `Optimizer::inline_switch` relies on this to produce good code,
                                // though not for correctness.
                            } else if target == stmt_index + 1 {
                                // Jumps to the statement after the switch can be performed by
                                // breaking from the switch itself. Breaks from the last arm don't
                                // have to be emitted.
                                if i != arms.len() - 1 {
                                    children.push(Statement::Break { block_id: id });
                                }
                            } else {
                                self.emit_jump(
                                    RequirementKey::Switch { stmt_index, key },
                                    &mut children,
                                );
                            }
                            (key, children)
                        })
                        .collect(),
                });
            }
        }
    }

    fn emit_jump(&mut self, key: RequirementKey, out: &mut Vec<Statement<'code>>) {
        let Some(imp) = self.jump_implementations.get(&key) else {
            panic!("missing jump implementation for {key:?}");
        };

        match *imp {
            RequirementImplementation::Break { block_id } => {
                out.push(Statement::Break { block_id })
            }
            RequirementImplementation::Continue { block_id } => {
                out.push(Statement::Continue { block_id })
            }
            RequirementImplementation::ContinueToDispatcher { block_id, selector } => {
                out.push(Statement::Basic {
                    index: None,
                    stmt: BasicStatement::Assign {
                        target: self.selector(),
                        value: self.arena.int(selector),
                    },
                });
                out.push(Statement::Continue { block_id })
            }
            RequirementImplementation::Try { .. } => {
                panic!("jump cannot be implemented with try")
            }
        }
    }

    fn selector(&self) -> ExprId {
        // This pass runs after variables are merged, so we need to explicitly use the same version
        // for all selectors. That's not *quite* correct in the sense that this can merge
        // independent selectors, but later passes are prepared to deal with that.
        self.arena.alloc(Expression::Variable(Variable {
            name: VariableName {
                id: 0,
                namespace: VariableNamespace::Selector,
            },
            version: self.unique_selector_id,
        }))
    }
}
