use crate::ast::{
    Arena, Catch, ExprId, Expression, GroupId, IrDef, Statement, StmtGroup, StmtMeta, Variable,
    Version,
};
use crate::structured::{self, CatchMeta};
use alloc::fmt;
use bitvec::vec::BitVec;
use core::ops::Range;
use rustc_hash::{FxHashMap, FxHashSet};

pub struct Output {
    pub program: StmtGroup<Ir>,
    pub var_info: FxHashMap<Version, VariableInfo>,
}

pub struct Ir;

impl IrDef for Ir {
    type Meta = Meta;
    type BasicMeta = IndexMeta;
    type BlockMeta = BlockMeta;
    type ContinueMeta = IndexMeta;
    type BreakMeta = IndexMeta;
    type SwitchMeta = IndexMeta;
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
pub enum IndexMeta {
    Synthetic,
    Real {
        index: usize,
        // Which of the `try` blocks containing this statement are active. This is quadratic if
        // there are many nested `try` blocks, but O(n log n) solutions like persistent Merkle trees
        // have a bigger constant factor in practice.
        active_tries: BitVec,
    },
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

impl fmt::Display for IndexMeta {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Synthetic => write!(f, ".syn "),
            Self::Real {
                index,
                active_tries,
            } => {
                if !active_tries.is_empty() {
                    write!(f, "try:")?;
                    for bit in active_tries {
                        write!(f, "{}", *bit as u32)?;
                    }
                    write!(f, " ")?;
                }
                write!(f, ".{index} ")
            }
        }
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
        first_unhandled_stmt: 0,
        last_stmt_active_tries: BitVec::new(),
        try_depth: 0,
        try_events: Vec::new(),
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
    first_unhandled_stmt: usize,
    last_stmt_active_tries: BitVec,
    try_depth: usize,
    // `try_events[index]` contains the list of bits to flip in `active_tries` at statement `index`.
    try_events: Vec<Vec<usize>>,
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
            .map(|stmt_meta| self.handle_stmt(stmt_meta.stmt))
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
            Statement::Basic {
                stmt,
                meta: index_meta,
            } => {
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
                    stmt: Statement::Basic {
                        stmt,
                        meta: self.map_index_meta(index_meta),
                    },
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

            Statement::Continue { group_id, meta } => StmtMeta {
                stmt: Statement::Continue {
                    group_id,
                    meta: self.map_index_meta(meta),
                },
                meta: Meta {
                    measure: 1,
                    access_range: self.next_access_id..self.next_access_id,
                    is_divergent: true,
                },
            },

            Statement::Break { group_id, meta } => {
                self.groups_with_breaks.insert(group_id);
                StmtMeta {
                    stmt: Statement::Break {
                        group_id,
                        meta: self.map_index_meta(meta),
                    },
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

            Statement::Switch {
                id,
                key,
                arms,
                meta: index_meta,
            } => {
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
                    stmt: Statement::Switch {
                        id,
                        key,
                        arms,
                        meta: self.map_index_meta(index_meta),
                    },
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

                assert_eq!(
                    catches.len(),
                    1,
                    "try should have exactly one catch at this point"
                );
                for active_range in &catches[0].meta.active_index_ranges {
                    if active_range.end >= self.try_events.len() {
                        self.try_events.resize(active_range.end + 1, Vec::new());
                    }
                    for index in [active_range.start, active_range.end] {
                        self.try_events[index].push(self.try_depth);
                    }
                }

                self.try_depth += 1;
                let (try_, try_meta) = self.handle_group(try_);
                self.try_depth -= 1;

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

    fn map_index_meta(&mut self, meta: structured::IndexMeta) -> IndexMeta {
        match meta.index {
            structured::Index::Synthetic => IndexMeta::Synthetic,
            structured::Index::Real(index) => {
                // Allows `index` to be `self.first_unhandled_stmt - 1`, i.e. have the same index as
                // the last statement. Occasionally used for generated, but not 100% synthetic code,
                // like `switch` instructions.
                assert!(
                    index + 1 >= self.first_unhandled_stmt,
                    "non-monotonically-increasing index"
                );

                // This is very ugly. I'm sorry.
                if self.first_unhandled_stmt < self.try_events.len() {
                    let index_range =
                        self.first_unhandled_stmt..(index + 1).min(self.try_events.len());
                    for try_index in self.try_events[index_range].iter().flatten().copied() {
                        if try_index >= self.last_stmt_active_tries.len() {
                            self.last_stmt_active_tries.resize(try_index + 1, false);
                        }
                        let mut bit = self.last_stmt_active_tries.get_mut(try_index).unwrap();
                        *bit = !*bit;
                    }
                }
                self.last_stmt_active_tries.resize(self.try_depth, false);
                self.first_unhandled_stmt = index + 1;

                IndexMeta::Real {
                    index,
                    active_tries: self.last_stmt_active_tries.clone(),
                }
            }
        }
    }
}
