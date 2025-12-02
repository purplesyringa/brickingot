use crate::ast::{
    Arena, Catch, ExprId, Expression, GroupId, IrDef, Statement, StmtGroup, StmtMeta, Variable,
    Version,
};
use crate::structured::{self, CatchMeta};
use alloc::fmt;
use core::ops::Range;
use rustc_hash::{FxHashMap, FxHashSet};

pub struct Output {
    pub program: StmtGroup<Ir>,
    pub var_info: FxHashMap<Version, VariableInfo>,
}

pub struct Ir;

impl IrDef for Ir {
    type Meta = Meta;
    type BlockMeta = BlockMeta;
    type CatchMeta = CatchMeta;
}

#[derive(Debug)]
pub struct Meta {
    // A "size" of the subtree. Doesn't need to be connected to any "real" size, except that:
    //
    // 1. It must be strictly monotonic over subtrees, i.e. the measure of a node must be strictly
    //    less than the measure of its parent.
    // 2. Isomorphic trees must have equal measures.
    //
    // Ideally, different random trees should also have different measures. Used as an asymptotic
    // optimization for locating `finally` blocks.
    pub measure: usize,
    // Range of variable accesses located entirely within this statement.
    pub access_range: Range<usize>,
    pub is_divergent: bool,
}

#[derive(Debug)]
pub struct BlockMeta {
    pub has_break: bool,
}

pub struct VariableInfo {
    pub use_range: Range<usize>,
    pub use_count: usize,
}

impl fmt::Display for Meta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "measure={} ", self.measure)?;
        if self.is_divergent {
            write!(f, "divergent ")?;
        }
        Ok(())
    }
}

impl fmt::Display for BlockMeta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.has_break {
            write!(f, "has_break ")?;
        }
        Ok(())
    }
}

pub fn analyze(arena: &Arena<'_>, ir: structured::Program) -> Output {
    let mut analyzer = Analyzer {
        arena,
        groups_with_breaks: FxHashSet::default(),
        next_access_id: 0,
        var_info: FxHashMap::default(),
    };
    let program = analyzer.handle_group(ir).0;
    Output {
        program,
        var_info: analyzer.var_info,
    }
}

struct Analyzer<'arena, 'code> {
    arena: &'arena Arena<'code>,
    groups_with_breaks: FxHashSet<GroupId>,
    next_access_id: usize,
    var_info: FxHashMap<Version, VariableInfo>,
}

impl Analyzer<'_, '_> {
    fn handle_group(&mut self, group: StmtGroup<structured::Ir>) -> (StmtGroup<Ir>, Meta) {
        let mut meta = Meta {
            measure: 1,
            access_range: self.next_access_id..0,
            is_divergent: false,
        };
        let children = group
            .children
            .into_iter()
            .map(|stmt| self.handle_stmt(stmt))
            .inspect(|stmt_meta| {
                meta.measure += stmt_meta.meta.measure;
                meta.is_divergent = stmt_meta.meta.is_divergent;
            })
            .collect();
        meta.access_range.end = self.next_access_id;
        (
            StmtGroup {
                id: group.id,
                children,
            },
            meta,
        )
    }

    fn handle_stmt(&mut self, stmt: Statement<structured::Ir>) -> StmtMeta<Ir> {
        match stmt {
            Statement::Basic { stmt, .. } => {
                let mut meta = Meta {
                    measure: 1,
                    access_range: self.next_access_id..0,
                    is_divergent: stmt.is_divergent(),
                };
                for expr in stmt.subexprs() {
                    self.handle_expr(expr);
                }
                meta.access_range.end = self.next_access_id;
                StmtMeta {
                    stmt: Statement::basic(stmt),
                    meta,
                }
            }

            Statement::Block { body, .. } => {
                let (body, mut meta) = self.handle_group(body);
                let has_break = self.groups_with_breaks.remove(&body.id);
                meta.is_divergent &= !has_break;
                StmtMeta {
                    stmt: Statement::Block {
                        body,
                        meta: BlockMeta { has_break },
                    },
                    meta,
                }
            }

            Statement::Continue { group_id, .. } => StmtMeta {
                stmt: Statement::continue_(group_id),
                meta: Meta {
                    measure: 1,
                    access_range: self.next_access_id..self.next_access_id,
                    is_divergent: true,
                },
            },

            Statement::Break { group_id, .. } => {
                self.groups_with_breaks.insert(group_id);
                StmtMeta {
                    stmt: Statement::break_(group_id),
                    meta: Meta {
                        measure: 1,
                        access_range: self.next_access_id..self.next_access_id,
                        is_divergent: true,
                    },
                }
            }

            Statement::If {
                condition,
                then,
                else_,
                ..
            } => {
                let mut access_range = self.next_access_id..0;
                self.handle_expr(condition);
                access_range.end = self.next_access_id;
                let (then, then_meta) = self.handle_group(then);
                assert!(
                    else_.children.is_empty(),
                    "shouldn't have anything in else yet",
                );
                let else_ = StmtGroup {
                    id: else_.id,
                    children: Vec::new(),
                };
                StmtMeta {
                    stmt: Statement::if_(condition, then, else_),
                    meta: Meta {
                        measure: then_meta.measure,
                        access_range,
                        is_divergent: false, // `else` is empty
                    },
                }
            }

            Statement::Switch { id, key, arms, .. } => {
                let mut meta = Meta {
                    measure: 1,
                    access_range: self.next_access_id..0,
                    is_divergent: false,
                };
                self.handle_expr(key);
                let arms = arms
                    .into_iter()
                    .map(|(value, body)| {
                        let (arm_body, arm_meta) = self.handle_group(body);
                        meta.measure += arm_meta.measure;
                        meta.is_divergent = arm_meta.is_divergent;
                        (value, arm_body)
                    })
                    .collect();
                meta.access_range.end = self.next_access_id;
                let has_break = self.groups_with_breaks.remove(&id);
                meta.is_divergent &= !has_break;
                StmtMeta {
                    stmt: Statement::switch(id, key, arms),
                    meta,
                }
            }

            Statement::Try {
                try_,
                catches,
                finally,
                ..
            } => {
                let mut meta = Meta {
                    measure: 1,
                    access_range: self.next_access_id..0,
                    is_divergent: false,
                };

                let (try_, try_meta) = self.handle_group(try_);
                meta.measure += try_meta.measure;
                meta.is_divergent = try_meta.is_divergent;

                let catches = catches
                    .into_iter()
                    .map(|catch| {
                        let (catch_body, catch_meta) = self.handle_group(catch.body);
                        meta.measure += catch_meta.measure;
                        meta.is_divergent &= catch_meta.is_divergent;
                        self.handle_var(catch.value_var);
                        Catch {
                            class: catch.class,
                            value_var: catch.value_var,
                            body: catch_body,
                            meta: catch.meta,
                        }
                    })
                    .collect();

                assert!(
                    finally.children.is_empty(),
                    "shouldn't have anything in finally yet",
                );
                let finally = StmtGroup {
                    id: finally.id,
                    children: Vec::new(),
                };

                meta.access_range.end = self.next_access_id;

                StmtMeta {
                    stmt: Statement::try_(try_, catches, finally),
                    meta,
                }
            }
        }
    }

    fn handle_expr(&mut self, expr_id: ExprId) {
        if let Expression::Variable(var) = self.arena[expr_id] {
            self.handle_var(var);
        }
        for sub_expr_id in self.arena[expr_id].subexprs() {
            self.handle_expr(sub_expr_id);
        }
    }

    fn handle_var(&mut self, var: Variable) {
        let var_info = self.var_info.entry(var.version).or_insert(VariableInfo {
            use_range: self.next_access_id..0,
            use_count: 0,
        });
        var_info.use_range.end = self.next_access_id + 1;
        self.next_access_id += 1;
        var_info.use_count += 1;
    }
}
