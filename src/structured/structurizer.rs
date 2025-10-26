use super::{
    Catch, Statement,
    solver::{
        Node, RequirementImplementation, RequirementKey, compute_block_requirements,
        satisfy_block_requirements,
    },
};
use crate::ast::{
    Arena, BasicStatement, ExprId, Expression, Variable, VariableName, VariableNamespace,
};
use crate::linear;
use rustc_hash::FxHashMap;

pub fn structure_control_flow<'code>(
    arena: &Arena<'code>,
    linear_ir: linear::Program<'code>,
) -> Vec<Statement<'code>> {
    // If you're confused as to what's happening here, read this first:
    // https://purplesyringa.moe/blog/recovering-control-flow-structures-without-cfgs/. The post
    // does not cover this implementation in its entirety, but it's pretty close.
    // `compute_block_requirements` effectively generates the arrows, `satisfy_block_requirements`
    // effectively builds a tree, and everything else is glue and exception handling logic.
    let requirements = compute_block_requirements(&linear_ir);
    let (mut req_keys, req_values): (Vec<_>, _) = requirements.into_iter().unzip();

    let (tree, implementations, next_block_id) =
        satisfy_block_requirements(linear_ir.statements.len(), req_values);

    // Add keys for dynamically created dispatch jumps.
    let mut id = req_keys.len();
    req_keys.resize_with(implementations.len(), || {
        let key = RequirementKey::Dispatch { req_id: id };
        id += 1;
        key
    });

    let mut try_block_to_handler: FxHashMap<usize, usize> = FxHashMap::default();
    let mut jump_implementations = FxHashMap::default();
    let mut has_dispatch = false;
    for (key, imp) in req_keys.into_iter().zip(implementations) {
        if let RequirementImplementation::Try { block_id } = imp {
            let RequirementKey::Try { handler_index } = key else {
                panic!("unexpected key for try implementation");
            };
            assert!(
                try_block_to_handler
                    .insert(block_id, handler_index)
                    .is_none(),
                "multiple handlers per try block"
            );
        } else {
            if let RequirementKey::Dispatch { .. } = key {
                has_dispatch = true;
            }
            jump_implementations.insert(key, imp);
        }
    }

    let mut structurizer = Structurizer {
        arena,
        linear_ir,
        try_block_to_handler,
        jump_implementations,
        next_block_id,
        unique_selector_id: arena.alloc(Expression::Null), // doesn't matter, just a unique ID
    };

    let mut stmts = Vec::new();
    if has_dispatch {
        stmts.push(Statement::Basic(BasicStatement::Assign {
            target: structurizer.selector(),
            value: arena.int(0),
        }));
    }
    for node in tree {
        structurizer.emit_node(node, &mut stmts);
    }

    stmts
}

struct Structurizer<'arena, 'code> {
    arena: &'arena Arena<'code>,
    linear_ir: linear::Program<'code>,
    try_block_to_handler: FxHashMap<usize, usize>,
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

            Node::Try { id, children } => {
                let handler_index = self
                    .try_block_to_handler
                    .remove(&id)
                    .expect("try block without catch");
                let handler = self.linear_ir.exception_handlers[handler_index].clone();

                let mut catch_children = Vec::new();
                if let Some((stack0_version, exception0_version)) =
                    handler.stack0_exception0_copy_versions
                {
                    catch_children.push(Statement::Basic(BasicStatement::Assign {
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
                    }));
                }

                let key = RequirementKey::BackwardCatch { handler_index };
                if self.jump_implementations.contains_key(&key) {
                    self.emit_jump(key, &mut catch_children);
                }

                out.push(Statement::Try {
                    children: self.emit_tree(children),
                    catches: vec![Catch {
                        class: handler.class,
                        children: catch_children,
                    }],
                });
            }

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
                            let mut stmts = vec![Statement::Basic(BasicStatement::Assign {
                                target: self.selector(),
                                value: self.arena.int(0),
                            })];
                            self.emit_jump(
                                RequirementKey::Dispatch {
                                    req_id: target.jump_req_id,
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
            &mut self.linear_ir.statements[stmt_index],
            linear::Statement::Basic(BasicStatement::ReturnVoid),
        );

        match stmt {
            linear::Statement::Basic(stmt) => out.push(Statement::Basic(stmt)),

            linear::Statement::Jump { condition, .. } => {
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

            linear::Statement::Switch { key, arms, default } => {
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
                out.push(Statement::Basic(BasicStatement::Assign {
                    target: self.selector(),
                    value: self.arena.int(selector),
                }));
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
