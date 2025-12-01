use super::{
    CatchMeta, Index, IndexMeta, Ir, Program,
    solver::{
        Node, RequirementImplementation, RequirementKey, compute_group_requirements,
        satisfy_group_requirements,
    },
};
use crate::ast::{
    Arena, BasicStatement, Catch, ExprId, Expression, GroupId, Statement, StmtGroup, StmtList,
    Version,
};
use crate::{
    linear::{self, CatchHandler},
    var,
};
use rustc_hash::FxHashMap;

pub fn structure_control_flow<'code>(
    arena: &Arena<'code>,
    linear_ir: linear::Program<'code>,
) -> Program {
    // If you're confused as to what's happening here, read this first:
    // https://purplesyringa.moe/blog/recovering-control-flow-structures-without-cfgs/. The post
    // does not cover this implementation in its entirety, but it's pretty close.
    // `compute_group_requirements` effectively generates the arrows, `satisfy_group_requirements`
    // effectively builds a tree, and everything else is glue and exception handling logic.
    let requirements = compute_group_requirements(&linear_ir);
    let (mut req_keys, req_values): (Vec<_>, _) = requirements.into_iter().unzip();

    let (tree, implementations, next_group_id) =
        satisfy_group_requirements(linear_ir.statements.len(), req_values);

    // Add keys for dynamically created dispatch jumps.
    let mut id = req_keys.len();
    req_keys.resize_with(implementations.len(), || {
        let key = RequirementKey::Dispatch { req_id: id };
        id += 1;
        key
    });

    let mut try_block_to_handler: FxHashMap<GroupId, usize> = FxHashMap::default();
    let mut jump_implementations = FxHashMap::default();
    let mut has_dispatch = false;
    for (key, imp) in req_keys.into_iter().zip(implementations) {
        if let RequirementImplementation::Try { group_id } = imp {
            let RequirementKey::Try { handler_index } = key else {
                panic!("unexpected key for try implementation");
            };
            assert!(
                try_block_to_handler
                    .insert(group_id, handler_index)
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
        statements: linear_ir.statements,
        catch_handlers: linear_ir.catch_handlers.into_iter().map(Some).collect(),
        try_block_to_handler,
        jump_implementations,
        next_group_id,
        selector_version: arena.version(),
    };

    let mut children = structurizer.emit_tree(tree);
    if has_dispatch {
        children.insert(
            0,
            Statement::Basic {
                stmt: BasicStatement::Assign {
                    target: structurizer.selector(),
                    value: arena.int(0),
                },
                meta: IndexMeta::synthetic(),
            },
        );
    }
    StmtGroup {
        children,
        id: GroupId::ROOT,
    }
}

struct Structurizer<'arena, 'code> {
    arena: &'arena Arena<'code>,
    statements: Vec<linear::Statement>,
    catch_handlers: Vec<Option<CatchHandler<'code>>>,
    try_block_to_handler: FxHashMap<GroupId, usize>,
    jump_implementations: FxHashMap<RequirementKey, RequirementImplementation>,
    next_group_id: GroupId,
    selector_version: Version,
}

impl Structurizer<'_, '_> {
    fn emit_tree(&mut self, tree: Vec<Node>) -> StmtList<Ir> {
        // This does not need to be exact, but it turns out that computing the size is better than
        // using a rough estimate just because we're hammering the allocator too much otherwise.
        let capacity = tree
            .iter()
            .map(|node| match node {
                Node::Linear { stmt_range } => stmt_range.len(),
                _ => 1,
            })
            .sum();
        let mut stmts = Vec::with_capacity(capacity);
        for node in tree {
            self.emit_node(node, &mut stmts);
        }
        stmts
    }

    fn emit_node(&mut self, node: Node, out: &mut StmtList<Ir>) {
        match node {
            Node::Linear { stmt_range } => {
                for stmt_index in stmt_range {
                    self.emit_stmt(stmt_index, out);
                }
            }

            Node::Block { id, children } => {
                out.push(Statement::block(StmtGroup {
                    id,
                    children: self.emit_tree(children),
                }));
            }

            Node::Try { id, children } => {
                let children = self.emit_tree(children);

                let handler_index = self
                    .try_block_to_handler
                    .remove(&id)
                    .expect("try block without catch");
                let handler = self.catch_handlers[handler_index]
                    .take()
                    .expect("missing `catch` handler");

                let mut catch_children = Vec::new();
                if let Some(stmt) = handler.stack_value_copy {
                    catch_children.push(Statement::Basic {
                        stmt,
                        meta: IndexMeta::synthetic(),
                    });
                }
                let key = RequirementKey::BackwardCatch { handler_index };
                if self.jump_implementations.contains_key(&key) {
                    self.emit_jump(key, Index::Synthetic, &mut catch_children);
                }

                out.push(Statement::try_(
                    self.new_group(children),
                    vec![Catch {
                        class: handler.class.map(|s| crate::ast::String(s.0.to_owned())),
                        value_var: handler.value_var,
                        body: self.new_group(catch_children),
                        meta: CatchMeta {
                            active_index_ranges: handler.active_ranges,
                        },
                    }],
                    self.new_group(Vec::new()),
                ));
            }

            Node::DispatchSwitch { dispatch_targets } => {
                // Dispatch targets can never point to the statement after the switch, since such
                // jumps would be trivially lowered to a normal, non-dispatch jump to this `switch`.
                let id = self.next_group_id;
                self.next_group_id.0 += 1;
                out.push(Statement::Switch {
                    id,
                    key: self.selector(),
                    arms: dispatch_targets
                        .into_iter()
                        .map(|target| {
                            let mut children = vec![Statement::Basic {
                                stmt: BasicStatement::Assign {
                                    target: self.selector(),
                                    value: self.arena.int(0),
                                },
                                meta: IndexMeta::synthetic(),
                            }];
                            self.emit_jump(
                                RequirementKey::Dispatch {
                                    req_id: target.jump_req_id,
                                },
                                Index::Synthetic,
                                &mut children,
                            );
                            (Some(target.selector), self.new_group(children))
                        })
                        .collect(),
                    meta: IndexMeta::synthetic(),
                });
            }
        }
    }

    fn emit_stmt(&mut self, stmt_index: usize, out: &mut StmtList<Ir>) {
        // Need to replace with *something*, `return;` works fine. We could wrap all statements in
        // `Option`, but that's probably a bit too slow.
        let stmt = core::mem::replace(
            &mut self.statements[stmt_index],
            linear::Statement::Basic(BasicStatement::ReturnVoid),
        );

        let index = Index::Real(stmt_index);
        let meta = IndexMeta { index };

        match stmt {
            linear::Statement::Basic(stmt) => out.push(Statement::Basic { stmt, meta }),

            linear::Statement::Jump { condition, .. } => {
                let out = if let Expression::ConstInt(1) = self.arena[condition] {
                    out
                } else {
                    out.push(Statement::if_(
                        condition,
                        self.new_group(Vec::new()),
                        self.new_group(Vec::new()),
                    ));
                    let Some(Statement::If { then, .. }) = out.last_mut() else {
                        unreachable!()
                    };
                    &mut then.children
                };
                self.emit_jump(RequirementKey::Jump { stmt_index }, index, out);
            }

            linear::Statement::Switch { key, arms, default } => {
                // Switches are only guaranteed to have a quality lowering if the arms are sorted by
                // target.
                let mut arms: Vec<(Option<i32>, usize)> = core::iter::once((None, default))
                    .chain(arms.iter().map(|(key, target)| (Some(*key), *target)))
                    .collect();
                arms.sort_unstable_by_key(|(_, target)| *target);

                let id = self.next_group_id;
                self.next_group_id.0 += 1;
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
                                    children.push(Statement::Break { group_id: id, meta });
                                }
                            } else {
                                self.emit_jump(
                                    RequirementKey::Switch { stmt_index, key },
                                    index,
                                    &mut children,
                                );
                            }
                            (key, self.new_group(children))
                        })
                        .collect(),
                    meta,
                });
            }
        }
    }

    fn emit_jump(&mut self, key: RequirementKey, index: Index, out: &mut StmtList<Ir>) {
        let Some(imp) = self.jump_implementations.get(&key) else {
            panic!("missing jump implementation for {key:?}");
        };
        let meta = IndexMeta { index };

        match *imp {
            RequirementImplementation::Break { block_id } => {
                out.push(Statement::Break {
                    group_id: block_id,
                    meta,
                });
            }
            RequirementImplementation::Continue { block_id } => {
                out.push(Statement::Continue {
                    group_id: block_id,
                    meta,
                });
            }
            RequirementImplementation::ContinueToDispatcher { block_id, selector } => {
                out.push(Statement::Basic {
                    stmt: BasicStatement::Assign {
                        target: self.selector(),
                        value: self.arena.int(selector),
                    },
                    meta,
                });
                out.push(Statement::Continue {
                    group_id: block_id,
                    meta,
                });
            }
            RequirementImplementation::Try { .. } => {
                panic!("jump cannot be implemented with try");
            }
        }
    }

    fn selector(&self) -> ExprId {
        // This pass runs after variables are merged, so we need to explicitly use the same version
        // for all selectors. That's not *quite* correct in the sense that this can merge
        // independent selectors, but later passes are prepared to deal with that.
        self.arena.var(var!(selector0 v self.selector_version))
    }

    fn new_group(&mut self, children: StmtList<Ir>) -> StmtGroup<Ir> {
        let id = self.next_group_id;
        self.next_group_id.0 += 1;
        StmtGroup { id, children }
    }
}
