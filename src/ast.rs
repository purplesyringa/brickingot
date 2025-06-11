use core::fmt::{self, Display};
use displaydoc::Display;
use noak::reader::cpool::value::{Dynamic, MethodHandle};
use noak::MStr;

#[derive(Debug, Display)]
pub enum BasicStatement<'arena, 'code> {
    /// {target} = {value};
    Assign {
        target: BoxedExpr<'arena, 'code>,
        value: BoxedExpr<'arena, 'code>,
    },
    /// return {value};
    Return { value: BoxedExpr<'arena, 'code> },
    /// return;
    ReturnVoid,
    /// throw {exception};
    Throw { exception: BoxedExpr<'arena, 'code> },
    /// {0};
    Calculate(BoxedExpr<'arena, 'code>),
    /// lock {object};
    MonitorEnter { object: BoxedExpr<'arena, 'code> },
    /// unlock {object};
    MonitorExit { object: BoxedExpr<'arena, 'code> },
}

impl BasicStatement<'_, '_> {
    pub fn is_divergent(&self) -> bool {
        match self {
            Self::Assign { .. }
            | Self::Calculate(_)
            | Self::MonitorEnter { .. }
            | Self::MonitorExit { .. } => false,
            Self::Return { .. } | Self::ReturnVoid | Self::Throw { .. } => true,
        }
    }
}

pub type BoxedExpr<'arena, 'code> = &'arena mut Expression<'arena, 'code>;

#[derive(Clone, Copy)]
pub struct ArenaRef<'arena, 'code> {
    pub typed_arena: &'arena typed_arena::Arena<Expression<'arena, 'code>>,
}

impl<'arena, 'code> ArenaRef<'arena, 'code> {
    pub fn alloc(self, expr: Expression<'arena, 'code>) -> BoxedExpr<'arena, 'code> {
        self.typed_arena.alloc(expr)
    }

    pub fn stack(self, id: usize) -> BoxedExpr<'arena, 'code> {
        self.alloc(Expression::Variable {
            id,
            namespace: VariableNamespace::Stack,
        })
    }

    pub fn slot(self, id: usize) -> BoxedExpr<'arena, 'code> {
        self.alloc(Expression::Variable {
            id,
            namespace: VariableNamespace::Slot,
        })
    }

    pub fn tmp(self, id: usize) -> BoxedExpr<'arena, 'code> {
        self.alloc(Expression::Variable {
            id,
            namespace: VariableNamespace::Temporary,
        })
    }

    pub fn int(self, value: i32) -> BoxedExpr<'arena, 'code> {
        self.alloc(Expression::ConstInt(value))
    }

    pub fn null(self) -> BoxedExpr<'arena, 'code> {
        self.alloc(Expression::Null)
    }
}

#[derive(Debug, Display)]
pub enum Expression<'arena, 'code> {
    /// ({array})[{index}]
    ArrayElement {
        array: BoxedExpr<'arena, 'code>,
        index: BoxedExpr<'arena, 'code>,
    },
    /// ({array}).length
    ArrayLength { array: BoxedExpr<'arena, 'code> },
    /// new {element_type}{lengths:?}
    NewArray {
        element_type: Type<'code>,
        lengths: Vec<BoxedExpr<'arena, 'code>>,
    },
    /// new uninitialized {class}
    NewUninitialized { class: Str<'code> },
    /// null
    Null,
    /// {namespace}{id}
    Variable {
        id: usize,
        namespace: VariableNamespace,
    },
    /// {0}
    Field(Field<'arena, 'code>),
    /// {0}.class
    Class(Str<'code>),
    /// {0:?}
    DynamicConst(Dynamic<'code>),
    /// {0:?}
    ConstMethodHandle(MethodHandle<'code>),
    /// MethodType({descriptor:?})
    ConstMethodType { descriptor: &'code MStr },
    /// {0}b
    ConstByte(i8),
    /// {0}s
    ConstShort(i16),
    /// {0}i
    ConstInt(i32),
    /// {0}l
    ConstLong(i64),
    /// {0}f
    ConstFloat(f32),
    /// {0}d
    ConstDouble(f64),
    /// {0:?}
    ConstString(&'code MStr),
    /// ({object}) instanceof {class}
    InstanceOf {
        object: BoxedExpr<'arena, 'code>,
        class: Str<'code>,
    },
    /// ({class})({value})
    CastReference {
        value: BoxedExpr<'arena, 'code>,
        class: Str<'code>,
    },
    /// ({from} -> {to})({value})
    CastPrimitive {
        value: BoxedExpr<'arena, 'code>,
        from: PrimitiveType,
        to: PrimitiveType,
    },
    /// ({lhs}) {op} ({rhs})
    BinOp {
        op: BinOp,
        lhs: BoxedExpr<'arena, 'code>,
        rhs: BoxedExpr<'arena, 'code>,
    },
    /// {op}({argument})
    UnaryOp {
        op: UnaryOp,
        argument: BoxedExpr<'arena, 'code>,
    },
    /// {0}
    Call(Call<'arena, 'code>),
}

#[derive(Debug)]
pub struct Field<'arena, 'code> {
    // `None` for static fields
    pub object: Option<BoxedExpr<'arena, 'code>>,
    pub class: Str<'code>,
    pub name: Str<'code>,
    // JVM bytecode allows fields with equal names but different types to co-exist, Java
    // doesn't. Decompiling such code correctly requires us to track types.
    pub descriptor: Str<'code>,
}

impl Display for Field<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(object) = &self.object {
            write!(f, "({object}).")?;
        }
        write!(f, "{}::{}[{}]", self.class, self.name, self.descriptor)
    }
}

#[derive(Debug)]
pub struct Call<'arena, 'code> {
    pub method_name: Str<'code>,
    pub kind: CallKind<'arena, 'code>,
    pub arguments: Arguments<'arena, 'code>,
    // We retain method descriptors until codegen because we may need to insert casts to invoke the
    // correct overloads, and we can't perform data flow analysis until SSA-like independent
    // variables have been established. For example, consider the snippet
    //     static void f(Object o) {}
    //     static void f(String s) {}
    //     static void g(String s) { f((Object)o); }
    // ...where the explicit cast to `Object` does not emit `checkcast` becuase it's an upcast, and
    // the only piece of information that specifies the correct overload is the method signature.
    pub descriptor: Str<'code>,
}

#[derive(Debug)]
pub enum CallKind<'arena, 'code> {
    Static {
        class_or_interface: Str<'code>,
    },
    Method {
        class_or_interface: Str<'code>,
        object: BoxedExpr<'arena, 'code>,
        is_special: bool,
    },
    Dynamic {
        bootstrap_method_attr: u16,
    },
}

impl Display for Call<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            CallKind::Static { class_or_interface } => write!(f, "{class_or_interface}::")?,
            CallKind::Method {
                class_or_interface,
                object,
                is_special,
            } => {
                write!(f, "({object}).")?;
                if *is_special {
                    write!(f, "special ")?;
                }
                write!(f, "{class_or_interface}::")?;
            }
            CallKind::Dynamic {
                bootstrap_method_attr,
            } => write!(f, "indy #{bootstrap_method_attr} ")?,
        }
        write!(
            f,
            "{}[{}]({})",
            self.method_name, self.descriptor, self.arguments
        )
    }
}

#[derive(Debug)]
pub struct Arguments<'arena, 'code>(pub Vec<BoxedExpr<'arena, 'code>>);

impl Display for Arguments<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(arg) = self.0.get(0) {
            write!(f, "{arg}")?;
            for arg in &self.0[1..] {
                write!(f, ", {arg}")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Display)]
pub enum Type<'code> {
    /// {0}
    Reference(Str<'code>),
    /// {0}
    Primitive(PrimitiveType),
}

#[derive(Clone, Copy, Debug, Display)]
pub enum PrimitiveType {
    /// byte
    Byte,
    /// char
    Char,
    /// short
    Short,
    /// int
    Int,
    /// long
    Long,
    /// float
    Float,
    /// double
    Double,
}

impl PrimitiveType {
    pub fn size(self) -> usize {
        use PrimitiveType::*;
        match self {
            Byte | Char | Short | Int | Float => 1,
            Long | Double => 2,
        }
    }
}

#[derive(Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div { is_fp: bool },
    Rem { is_fp: bool },
    And,
    Or,
    Xor,
    Shl,
    Shr,
    UnsignedShr,
    Compare { fp_negative_on_nan: bool },
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Add => write!(f, "+"),
            Self::Sub => write!(f, "-"),
            Self::Mul => write!(f, "*"),
            Self::Div { is_fp: false } => write!(f, "/"),
            Self::Div { is_fp: true } => write!(f, "/fp"),
            Self::Rem { is_fp: false } => write!(f, "%"),
            Self::Rem { is_fp: true } => write!(f, "%fp"),
            Self::And => write!(f, "&"),
            Self::Or => write!(f, "|"),
            Self::Xor => write!(f, "^"),
            Self::Shl => write!(f, "<<"),
            Self::Shr => write!(f, ">>"),
            Self::UnsignedShr => write!(f, ">>>"),
            Self::Compare {
                fp_negative_on_nan: false,
            } => write!(f, "<=>"),
            Self::Compare {
                fp_negative_on_nan: true,
            } => write!(f, "<=>neg"),
            Self::Eq => write!(f, "=="),
            Self::Ne => write!(f, "!="),
            Self::Lt => write!(f, "<"),
            Self::Le => write!(f, "<="),
            Self::Gt => write!(f, ">"),
            Self::Ge => write!(f, ">="),
        }
    }
}

#[derive(Debug, Display)]
pub enum UnaryOp {
    /// -
    Neg,
}

#[derive(Clone, Copy, Debug, Display, Hash, PartialEq, Eq)]
pub enum VariableNamespace {
    /// slot
    Slot,
    /// stack
    Stack,
    /// tmp
    Temporary,
    /// selector
    Selector,
}

#[derive(Clone, Copy, Debug)]
pub struct Str<'code>(pub &'code MStr);

impl Display for Str<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.display())
    }
}
