use super::{
    CatchMeta, Index, IndexMeta, Ir, Program,
    solver::{
        Node, NodeId, RequirementImplementation, RequirementKey, compute_node_requirements,
        satisfy_node_requirements,
    },
};
use crate::ast::{
    Arena, BasicStatement, Catch, ExprId, Expression, GroupId, Statement, StmtGroup, StmtList,
    StmtMeta, Version,
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
    let requirements = compute_node_requirements(&linear_ir);
    let (mut req_keys, req_values): (Vec<_>, _) = requirements.into_iter().unzip();

    let (tree, implementations, n_node_ids) =
        satisfy_node_requirements(linear_ir.statements.len(), req_values);

    // Add keys for dynamically created dispatch jumps.
    let mut id = req_keys.len();
    req_keys.resize_with(implementations.len(), || {
        let key = RequirementKey::Dispatch { req_id: id };
        id += 1;
        key
    });

    let mut try_node_to_handler: FxHashMap<NodeId, usize> = FxHashMap::default();
    let mut jump_implementations = FxHashMap::default();
    let mut has_dispatch = false;
    for (key, imp) in req_keys.into_iter().zip(implementations) {
        if let RequirementImplementation::Try { node_id } = imp {
            let RequirementKey::Try { handler_index } = key else {
                panic!("unexpected key for try implementation");
            };
            assert!(
                try_node_to_handler.insert(node_id, handler_index).is_none(),
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
        node_id_to_group_id: vec![GroupId(u32::MAX); n_node_ids],
        try_node_to_handler,
        jump_implementations,
        next_group_id: GroupId::ROOT,
        selector_version: arena.version(),
    };

    let mut root = structurizer.emit_group(None, tree);
    if has_dispatch {
        root.children.insert(
            0,
            Statement::Basic {
                stmt: BasicStatement::Assign {
                    target: structurizer.selector(),
                    value: arena.int(0),
                },
                meta: IndexMeta::synthetic(),
            }
            .into(),
        );
    }
    root
}

struct Structurizer<'arena, 'code> {
    arena: &'arena Arena<'code>,
    statements: Vec<linear::Statement>,
    catch_handlers: Vec<Option<CatchHandler<'code>>>,
    node_id_to_group_id: Vec<GroupId>,
    try_node_to_handler: FxHashMap<NodeId, usize>,
    jump_implementations: FxHashMap<RequirementKey, RequirementImplementation>,
    next_group_id: GroupId,
    selector_version: Version,
}

impl Structurizer<'_, '_> {
    fn emit_group(&mut self, node_id: Option<NodeId>, children: Vec<Node>) -> StmtGroup<Ir> {
        let group_id = self.alloc_group_id();
        if let Some(node_id) = node_id {
            // Allocate a new group ID instead of reusing the node ID, since we require group IDs to
            // be ordered according to preorder traversal and want to insert new groups between node
            // IDs.
            self.node_id_to_group_id[node_id.0 as usize] = group_id;
        }
        StmtGroup {
            id: group_id,
            children: self.emit_list(children),
        }
    }

    fn emit_list(&mut self, list: Vec<Node>) -> StmtList<Ir> {
        // This does not need to be exact, but it turns out that computing the size is better than
        // using a rough estimate just because we're hammering the allocator too much otherwise.
        let capacity = list
            .iter()
            .map(|node| match node {
                Node::Linear { stmt_range } => stmt_range.len(),
                _ => 1,
            })
            .sum();
        let mut stmts = Vec::with_capacity(capacity);
        for node in list {
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

            Node::Block {
                id: node_id,
                children,
            } => {
                out.push(Statement::block(self.emit_group(Some(node_id), children)).into());
            }

            Node::Try { id, children } => {
                let try_ = self.emit_group(None, children);

                let handler_index = self
                    .try_node_to_handler
                    .remove(&id)
                    .expect("try block without catch");
                let handler = self.catch_handlers[handler_index]
                    .take()
                    .expect("missing `catch` handler");

                let mut catch = self.empty_group();
                if let Some(stmt) = handler.stack_value_copy {
                    catch.children.push(
                        Statement::Basic {
                            stmt,
                            meta: IndexMeta::synthetic(),
                        }
                        .into(),
                    );
                }
                let key = RequirementKey::BackwardCatch { handler_index };
                if self.jump_implementations.contains_key(&key) {
                    self.emit_jump(key, Index::Synthetic, &mut catch.children);
                }

                out.push(
                    Statement::try_(
                        try_,
                        vec![Catch {
                            class: handler.class.map(|s| crate::ast::String(s.0.to_owned())),
                            value_var: handler.value_var,
                            body: catch,
                            meta: CatchMeta {
                                active_index_ranges: handler.active_ranges,
                            },
                        }],
                        self.empty_group(),
                    )
                    .into(),
                );
            }

            Node::DispatchSwitch { dispatch_targets } => {
                // Dispatch targets can never point to the statement after the switch, since such
                // jumps would be trivially lowered to a normal, non-dispatch jump to this `switch`.
                let group_id = self.alloc_group_id();
                out.push(
                    Statement::Switch {
                        id: group_id,
                        key: self.selector(),
                        arms: dispatch_targets
                            .into_iter()
                            .map(|target| {
                                let mut body = self.empty_group();
                                body.children.push(
                                    Statement::Basic {
                                        stmt: BasicStatement::Assign {
                                            target: self.selector(),
                                            value: self.arena.int(0),
                                        },
                                        meta: IndexMeta::synthetic(),
                                    }
                                    .into(),
                                );
                                self.emit_jump(
                                    RequirementKey::Dispatch {
                                        req_id: target.jump_req_id,
                                    },
                                    Index::Synthetic,
                                    &mut body.children,
                                );
                                (Some(target.selector), body)
                            })
                            .collect(),
                        meta: IndexMeta::synthetic(),
                    }
                    .into(),
                );
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
            linear::Statement::Basic(stmt) => out.push(Statement::Basic { stmt, meta }.into()),

            linear::Statement::Jump { condition, .. } => {
                let out = if let Expression::ConstInt(1) = self.arena[condition] {
                    out
                } else {
                    out.push(
                        Statement::if_(condition, self.empty_group(), self.empty_group()).into(),
                    );
                    let Some(StmtMeta {
                        stmt: Statement::If { then, .. },
                        ..
                    }) = out.last_mut()
                    else {
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

                let group_id = self.alloc_group_id();

                let arms = arms
                    .iter()
                    .enumerate()
                    .map(|(i, &(key, target))| {
                        let mut body = self.empty_group();
                        if let Some((_, next_target)) = arms.get(i + 1)
                            && target == *next_target
                        {
                            // Allow arms to the same target to fallthrough, so that we get a nice
                            // `case 1: case 2: ... case n:` decompilation.
                            // `Optimizer::inline_switch` relies on this to produce good code,
                            // though not for correctness.
                        } else if target == stmt_index + 1 {
                            // Jumps to the statement after the switch can be performed by breaking
                            // from the switch itself. Breaks from the last arm don't have to be
                            // emitted.
                            if i != arms.len() - 1 {
                                body.children
                                    .push(Statement::Break { group_id, meta }.into());
                            }
                        } else {
                            self.emit_jump(
                                RequirementKey::Switch { stmt_index, key },
                                index,
                                &mut body.children,
                            );
                        }
                        (key, body)
                    })
                    .collect();

                out.push(
                    Statement::Switch {
                        id: group_id,
                        key,
                        arms,
                        meta,
                    }
                    .into(),
                );
            }
        }
    }

    fn emit_jump(&mut self, key: RequirementKey, index: Index, out: &mut StmtList<Ir>) {
        let Some(imp) = self.jump_implementations.get(&key) else {
            panic!("missing jump implementation for {key:?}");
        };
        let meta = IndexMeta { index };

        match *imp {
            RequirementImplementation::Break { node_id } => {
                out.push(
                    Statement::Break {
                        group_id: self.node_id_to_group_id[node_id.0 as usize],
                        meta,
                    }
                    .into(),
                );
            }
            RequirementImplementation::Continue { node_id } => {
                out.push(
                    Statement::Continue {
                        group_id: self.node_id_to_group_id[node_id.0 as usize],
                        meta,
                    }
                    .into(),
                );
            }
            RequirementImplementation::ContinueToDispatcher { node_id, selector } => {
                out.push(
                    Statement::Basic {
                        stmt: BasicStatement::Assign {
                            target: self.selector(),
                            value: self.arena.int(selector),
                        },
                        meta,
                    }
                    .into(),
                );
                out.push(
                    Statement::Continue {
                        group_id: self.node_id_to_group_id[node_id.0 as usize],
                        meta,
                    }
                    .into(),
                );
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

    fn alloc_group_id(&mut self) -> GroupId {
        let id = self.next_group_id;
        self.next_group_id.0 += 1;
        id
    }

    fn empty_group(&mut self) -> StmtGroup<Ir> {
        StmtGroup {
            id: self.alloc_group_id(),
            children: Vec::new(),
        }
    }
}
