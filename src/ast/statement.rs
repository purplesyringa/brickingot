use super::{Arena, DebugIr, ExprId, Str};
use core::fmt;
use derive_where::derive_where;
use noak::MStr;

pub trait MetaDef: fmt::Debug {
    type WithStmt<Ir: IrDef<Meta = Self>>: fmt::Debug + for<'code> DebugIr<'code>;
    fn display(&self) -> impl fmt::Display;
}

impl<T: fmt::Display + fmt::Debug> MetaDef for T {
    type WithStmt<Ir: IrDef<Meta = Self>> = StmtMeta<Ir>;
    fn display(&self) -> impl fmt::Display {
        self
    }
}

#[derive_where(Debug)]
pub struct StmtMeta<Ir: IrDef> {
    pub stmt: Statement<Ir>,
    pub meta: Ir::Meta,
}

#[derive(Debug)]
pub struct NoMeta;

impl MetaDef for NoMeta {
    type WithStmt<Ir: IrDef<Meta = Self>> = Statement<Ir>;
    fn display(&self) -> impl fmt::Display {
        ""
    }
}

pub trait IrDef {
    type Meta: MetaDef = NoMeta;
    type BasicMeta: MetaDef = !;
    type BlockMeta: MetaDef = !;
    type ContinueMeta: MetaDef = !;
    type BreakMeta: MetaDef = !;
    type IfMeta: MetaDef = !;
    type SwitchMeta: MetaDef = !;
    type TryMeta: MetaDef = !;
    type CatchMeta: MetaDef = NoMeta;
}

#[derive_where(Debug)]
pub enum Statement<Ir: IrDef> {
    Basic {
        stmt: BasicStatement,
        meta: Ir::BasicMeta,
    },
    Block {
        id: usize,
        children: StmtList<Ir>,
        meta: Ir::BlockMeta,
    },
    Continue {
        block_id: usize,
        meta: Ir::ContinueMeta,
    },
    Break {
        block_id: usize,
        meta: Ir::BreakMeta,
    },
    If {
        condition: ExprId,
        then_children: StmtList<Ir>,
        else_children: StmtList<Ir>,
        meta: Ir::IfMeta,
    },
    Switch {
        id: usize,
        key: ExprId,
        arms: Vec<(Option<i32>, StmtList<Ir>)>,
        meta: Ir::SwitchMeta,
    },
    Try {
        try_children: StmtList<Ir>,
        catches: Vec<Catch<Ir>>,
        finally_children: StmtList<Ir>,
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

    pub fn block(id: usize, children: StmtList<Ir>) -> Self
    where
        Ir: IrDef<BlockMeta = NoMeta>,
    {
        Self::Block {
            id,
            children,
            meta: NoMeta,
        }
    }

    pub fn continue_(block_id: usize) -> Self
    where
        Ir: IrDef<ContinueMeta = NoMeta>,
    {
        Self::Continue {
            block_id,
            meta: NoMeta,
        }
    }

    pub fn break_(block_id: usize) -> Self
    where
        Ir: IrDef<BreakMeta = NoMeta>,
    {
        Self::Break {
            block_id,
            meta: NoMeta,
        }
    }

    pub fn if_(condition: ExprId, then_children: StmtList<Ir>, else_children: StmtList<Ir>) -> Self
    where
        Ir: IrDef<IfMeta = NoMeta>,
    {
        Self::If {
            condition,
            then_children,
            else_children,
            meta: NoMeta,
        }
    }

    pub fn switch(id: usize, key: ExprId, arms: Vec<(Option<i32>, StmtList<Ir>)>) -> Self
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

    pub fn try_(
        try_children: StmtList<Ir>,
        catches: Vec<Catch<Ir>>,
        finally_children: StmtList<Ir>,
    ) -> Self
    where
        Ir: IrDef<TryMeta = NoMeta>,
    {
        Self::Try {
            try_children,
            catches,
            finally_children,
            meta: NoMeta,
        }
    }
}

pub type StmtList<Ir> = Vec<<<Ir as IrDef>::Meta as MetaDef>::WithStmt<Ir>>;

#[derive(Debug)]
pub enum BasicStatement {
    Assign { target: ExprId, value: ExprId },
    Return { value: ExprId },
    ReturnVoid,
    Throw { exception: ExprId },
    Calculate(ExprId),
    MonitorEnter { object: ExprId },
    MonitorExit { object: ExprId },
}

#[derive_where(Debug)]
pub struct Catch<Ir: IrDef> {
    pub class: Option<super::String>, // don't want to pollute the types with lifetimes
    pub children: StmtList<Ir>,
    pub meta: Ir::CatchMeta,
}

impl<Ir: IrDef> Catch<Ir> {
    pub fn new(class: Option<super::String>, children: StmtList<Ir>) -> Self
    where
        Ir: IrDef<CatchMeta = NoMeta>,
    {
        Self {
            class,
            children,
            meta: NoMeta,
        }
    }
}

impl<'code, Ir: IrDef> DebugIr<'code> for StmtMeta<Ir> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        write!(f, "{}{}", self.meta.display(), arena.debug(&self.stmt))
    }
}

impl<'code, Ir: IrDef> DebugIr<'code> for Statement<Ir> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        match self {
            Self::Basic { stmt, meta } => write!(f, "{}{}", meta.display(), arena.debug(stmt)),
            Self::Block { id, children, meta } => {
                writeln!(f, "{}block #{id} {{", meta.display())?;
                write!(f, "{}", arena.debug(&children))?;
                write!(f, "}} block #{id}")
            }
            Self::Continue { block_id, meta } => {
                write!(f, "{}continue #{block_id};", meta.display())
            }
            Self::Break { block_id, meta } => write!(f, "{}break #{block_id};", meta.display()),
            Self::If {
                condition,
                then_children,
                else_children,
                meta,
            } => {
                writeln!(f, "{}if ({}) {{", meta.display(), arena.debug(condition))?;
                write!(f, "{}", arena.debug(&then_children))?;
                if !else_children.is_empty() {
                    writeln!(f, "}} else {{")?;
                    write!(f, "{}", arena.debug(&else_children))?;
                }
                write!(f, "}}")
            }
            Self::Switch {
                id,
                key,
                arms,
                meta,
            } => {
                writeln!(
                    f,
                    "{}switch #{id} ({}) {{",
                    meta.display(),
                    arena.debug(key)
                )?;
                for (value, children) in arms {
                    match value {
                        Some(value) => writeln!(f, "case {value}:")?,
                        None => writeln!(f, "default:")?,
                    }
                    write!(f, "{}", arena.debug(&children))?;
                }
                write!(f, "}} switch #{id};")
            }

            Self::Try {
                try_children,
                catches,
                finally_children,
                meta,
            } => {
                writeln!(f, "{}try {{", meta.display())?;
                write!(f, "{}", arena.debug(&try_children))?;
                for catch in catches {
                    writeln!(
                        f,
                        "}} catch ({}{}) {{",
                        catch.meta.display(),
                        catch
                            .class
                            .as_ref()
                            .map(|s| Str(&s.0))
                            .unwrap_or(Str(MStr::from_mutf8(b"Throwable").unwrap())),
                    )?;
                    write!(f, "{}", arena.debug(&catch.children))?;
                }
                if !finally_children.is_empty() {
                    writeln!(f, "}} finally {{")?;
                    write!(f, "{}", arena.debug(&finally_children))?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl<'code> DebugIr<'code> for BasicStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
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
