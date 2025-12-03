use super::{
    Arena, DebugIr, ExprId, Str, Variable,
    isomorphism::{Isomorphic, derive_deftly_template_Isomorphic},
};
use core::fmt;
use derive_deftly::Deftly;
use derive_where::derive_where;
use displaydoc::Display;
use noak::MStr;

pub trait MetaDef: fmt::Debug + fmt::Display {}
impl<T: fmt::Debug + fmt::Display> MetaDef for T {}

#[derive_where(Debug)]
#[derive(Deftly)]
#[derive_deftly(Isomorphic)]
#[deftly(derive_where = "Ir: IsomorphicIrDef")]
pub struct StmtMeta<Ir: IrDef> {
    pub stmt: Statement<Ir>,
    pub meta: Ir::Meta,
}

#[derive(Debug, Deftly)]
#[derive_deftly(Isomorphic)]
pub struct NoMeta;

impl fmt::Display for NoMeta {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

impl<Ir: IrDef<Meta = NoMeta>> From<Statement<Ir>> for StmtMeta<Ir> {
    fn from(stmt: Statement<Ir>) -> Self {
        Self { stmt, meta: NoMeta }
    }
}

pub trait IrDef {
    type Meta: MetaDef = NoMeta;
    type BasicMeta: MetaDef = NoMeta;
    type BlockMeta: MetaDef = NoMeta;
    type ContinueMeta: MetaDef = NoMeta;
    type BreakMeta: MetaDef = NoMeta;
    type IfMeta: MetaDef = NoMeta;
    type SwitchMeta: MetaDef = NoMeta;
    type TryMeta: MetaDef = NoMeta;
    type CatchMeta: MetaDef = NoMeta;
}

trait IsomorphicIrDef = Sized
    + IrDef<
        Meta: Isomorphic,
        BasicMeta: Isomorphic,
        BlockMeta: Isomorphic,
        ContinueMeta: Isomorphic,
        BreakMeta: Isomorphic,
        IfMeta: Isomorphic,
        SwitchMeta: Isomorphic,
        TryMeta: Isomorphic,
        CatchMeta: Isomorphic,
    >;

#[derive_where(Debug)]
#[derive(Deftly)]
#[derive_deftly(Isomorphic)]
#[deftly(derive_where = "Ir: IsomorphicIrDef")]
pub enum Statement<Ir: IrDef> {
    Basic {
        stmt: BasicStatement,
        meta: Ir::BasicMeta,
    },
    Block {
        body: StmtGroup<Ir>,
        meta: Ir::BlockMeta,
    },
    Continue {
        group_id: GroupId,
        meta: Ir::ContinueMeta,
    },
    Break {
        group_id: GroupId,
        meta: Ir::BreakMeta,
    },
    If {
        condition: ExprId,
        then: StmtGroup<Ir>,
        else_: StmtGroup<Ir>,
        meta: Ir::IfMeta,
    },
    Switch {
        id: GroupId,
        key: ExprId,
        arms: Vec<(Option<i32>, StmtGroup<Ir>)>,
        meta: Ir::SwitchMeta,
    },
    Try {
        try_: StmtGroup<Ir>,
        catches: Vec<Catch<Ir>>,
        finally: StmtGroup<Ir>,
        meta: Ir::TryMeta,
    },
}

impl<Ir: IrDef> Statement<Ir> {
    pub fn basic(stmt: BasicStatement) -> Self
    where
        Ir: IrDef<BasicMeta = NoMeta>,
    {
        Self::Basic { stmt, meta: NoMeta }
    }

    pub fn block(body: StmtGroup<Ir>) -> Self
    where
        Ir: IrDef<BlockMeta = NoMeta>,
    {
        Self::Block { body, meta: NoMeta }
    }

    pub fn continue_(group_id: GroupId) -> Self
    where
        Ir: IrDef<ContinueMeta = NoMeta>,
    {
        Self::Continue {
            group_id,
            meta: NoMeta,
        }
    }

    pub fn break_(group_id: GroupId) -> Self
    where
        Ir: IrDef<BreakMeta = NoMeta>,
    {
        Self::Break {
            group_id,
            meta: NoMeta,
        }
    }

    pub fn if_(condition: ExprId, then: StmtGroup<Ir>, else_: StmtGroup<Ir>) -> Self
    where
        Ir: IrDef<IfMeta = NoMeta>,
    {
        Self::If {
            condition,
            then,
            else_,
            meta: NoMeta,
        }
    }

    pub fn switch(id: GroupId, key: ExprId, arms: Vec<(Option<i32>, StmtGroup<Ir>)>) -> Self
    where
        Ir: IrDef<SwitchMeta = NoMeta>,
    {
        Self::Switch {
            id,
            key,
            arms,
            meta: NoMeta,
        }
    }

    pub fn try_(try_: StmtGroup<Ir>, catches: Vec<Catch<Ir>>, finally: StmtGroup<Ir>) -> Self
    where
        Ir: IrDef<TryMeta = NoMeta>,
    {
        Self::Try {
            try_,
            catches,
            finally,
            meta: NoMeta,
        }
    }
}

#[derive(Clone, Copy, Debug, Display, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// {0}
pub struct GroupId(pub u32);

impl GroupId {
    pub const ROOT: GroupId = GroupId(0);
}

pub type StmtList<Ir> = Vec<StmtMeta<Ir>>;

#[derive(Deftly)]
#[derive_where(Debug)]
#[derive_deftly(Isomorphic)]
#[deftly(derive_where = "Ir: IsomorphicIrDef")]
pub struct StmtGroup<Ir: IrDef> {
    #[deftly(definition)]
    pub id: GroupId,
    pub children: StmtList<Ir>,
}

#[derive(Debug, Deftly)]
#[derive_deftly(Isomorphic)]
pub enum BasicStatement {
    Assign { target: ExprId, value: ExprId },
    Return { value: ExprId },
    ReturnVoid,
    Throw { exception: ExprId },
    Calculate(ExprId),
    MonitorEnter { object: ExprId },
    MonitorExit { object: ExprId },
}

#[derive(Deftly)]
#[derive_where(Debug)]
#[derive_deftly(Isomorphic)]
#[deftly(derive_where = "Ir: IsomorphicIrDef")]
pub struct Catch<Ir: IrDef> {
    pub class: Option<super::String>, // don't want to pollute the types with lifetimes
    pub value_var: Variable,
    pub body: StmtGroup<Ir>,
    #[deftly(ignore)]
    pub meta: Ir::CatchMeta,
}

impl<Ir: IrDef> Catch<Ir> {
    pub fn new(class: Option<super::String>, value_var: Variable, body: StmtGroup<Ir>) -> Self
    where
        Ir: IrDef<CatchMeta = NoMeta>,
    {
        Self {
            class,
            value_var,
            body,
            meta: NoMeta,
        }
    }
}

impl<Ir: IrDef> DebugIr for StmtMeta<Ir> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result {
        write!(f, "{}{}", self.meta, arena.debug(&self.stmt))
    }
}

impl<Ir: IrDef> DebugIr for Statement<Ir> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result {
        match self {
            Self::Basic { stmt, meta } => write!(f, "{meta}{}", arena.debug(stmt)),
            Self::Block { body, meta } => {
                write!(f, "{meta}block {}", arena.debug(body))
            }
            Self::Continue { group_id, meta } => {
                write!(f, "{meta}continue #{group_id};")
            }
            Self::Break { group_id, meta } => write!(f, "{meta}break #{group_id};"),
            Self::If {
                condition,
                then,
                else_,
                meta,
            } => {
                write!(
                    f,
                    "{meta}if ({}) {}",
                    arena.debug(condition),
                    arena.debug(then),
                )?;
                if !else_.children.is_empty() {
                    write!(f, " else {}", arena.debug(else_))?;
                }
                Ok(())
            }
            Self::Switch {
                id,
                key,
                arms,
                meta,
            } => {
                writeln!(f, "{meta}switch #{id} ({}) {{", arena.debug(key))?;
                for (value, body) in arms {
                    match value {
                        Some(value) => write!(f, "case {value}: ")?,
                        None => write!(f, "default: ")?,
                    }
                    writeln!(f, "{}", arena.debug(&body))?;
                }
                write!(f, "}} switch #{id};")
            }

            Self::Try {
                try_,
                catches,
                finally,
                meta,
            } => {
                write!(f, "{meta}try {}", arena.debug(try_))?;
                for catch in catches {
                    write!(
                        f,
                        " catch ({}{} {}) {}",
                        catch.meta,
                        catch
                            .class
                            .as_ref()
                            .map(|s| Str(&s.0))
                            .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
                        catch.value_var,
                        arena.debug(&catch.body),
                    )?;
                }
                if !finally.children.is_empty() {
                    write!(f, " finally {}", arena.debug(finally))?;
                }
                Ok(())
            }
        }
    }
}

impl<Ir: IrDef> DebugIr for StmtGroup<Ir> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result {
        writeln!(f, "#{} {{", self.id)?;
        for stmt in &self.children {
            writeln!(f, "{}", arena.debug(stmt))?;
        }
        write!(f, "}} #{}", self.id)
    }
}

impl DebugIr for BasicStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result {
        match self {
            Self::Assign { target, value } => {
                write!(f, "{} = {};", arena.debug(target), arena.debug(value))
            }
            Self::Return { value } => write!(f, "return {};", arena.debug(value)),
            Self::ReturnVoid => write!(f, "return;"),
            Self::Throw { exception } => write!(f, "throw {};", arena.debug(exception)),
            Self::Calculate(value) => write!(f, "{};", arena.debug(value)),
            Self::MonitorEnter { object } => write!(f, "lock {};", arena.debug(object)),
            Self::MonitorExit { object } => write!(f, "unlock {};", arena.debug(object)),
        }
    }
}
