use core::fmt::{self, Display};
use displaydoc::Display;
use noak::MStr;
use noak::reader::cpool::value::{Dynamic, MethodHandle};

#[derive(Debug, Display)]
pub enum BasicStatement<'a> {
    /// {target} = {value};
    Assign {
        target: Box<Expression<'a>>,
        value: Box<Expression<'a>>,
    },
    /// return {value};
    Return { value: Box<Expression<'a>> },
    /// return;
    ReturnVoid,
    /// throw {exception};
    Throw { exception: Box<Expression<'a>> },
    /// {0};
    Calculate(Box<Expression<'a>>),
    /// lock {object};
    MonitorEnter { object: Box<Expression<'a>> },
    /// unlock {object};
    MonitorExit { object: Box<Expression<'a>> },
}

#[derive(Debug, Display)]
pub enum Expression<'a> {
    /// ({array})[{index}]
    ArrayElement {
        array: Box<Expression<'a>>,
        index: Box<Expression<'a>>,
    },
    /// ({array}).length
    ArrayLength { array: Box<Expression<'a>> },
    /// new {element_type}{lengths:?}
    NewArray {
        element_type: Type<'a>,
        lengths: Vec<Box<Expression<'a>>>,
    },
    /// new uninitialized {class}
    NewUninitialized { class: Str<'a> },
    /// null
    Null,
    /// {namespace}{id}
    Variable {
        id: usize,
        namespace: VariableNamespace,
    },
    /// {0}
    Field(Field<'a>),
    /// {0}.class
    Class(Str<'a>),
    /// {0:?}
    DynamicConst(Dynamic<'a>),
    /// {0:?}
    ConstMethodHandle(MethodHandle<'a>),
    /// MethodType({descriptor:?})
    ConstMethodType { descriptor: &'a MStr },
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
    ConstString(&'a MStr),
    /// ({object}) instanceof {class}
    InstanceOf {
        object: Box<Expression<'a>>,
        class: Str<'a>,
    },
    /// ({class})({value})
    CastReference {
        value: Box<Expression<'a>>,
        class: Str<'a>,
    },
    /// ({from} -> {to})({value})
    CastPrimitive {
        value: Box<Expression<'a>>,
        from: PrimitiveType,
        to: PrimitiveType,
    },
    /// ({lhs}) {op} ({rhs})
    BinOp {
        op: BinOp,
        lhs: Box<Expression<'a>>,
        rhs: Box<Expression<'a>>,
    },
    /// {op}({argument})
    UnaryOp {
        op: UnaryOp,
        argument: Box<Expression<'a>>,
    },
    /// {0}
    Call(Call<'a>),
}

#[derive(Debug)]
pub struct Field<'a> {
    // `None` for static fields
    pub object: Option<Box<Expression<'a>>>,
    pub class: Str<'a>,
    pub name: Str<'a>,
    // JVM bytecode allows fields with equal names but different types to co-exist, Java
    // doesn't. Decompiling such code correctly requires us to track types.
    pub descriptor: Str<'a>,
}

impl Display for Field<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(object) = &self.object {
            write!(f, "({object}).")?;
        }
        write!(f, "{}::{}[{}]", self.class, self.name, self.descriptor)
    }
}

#[derive(Debug)]
pub struct Call<'a> {
    pub method_name: Str<'a>,
    pub kind: CallKind<'a>,
    pub arguments: Arguments<'a>,
    // We retain method descriptors until codegen because we may need to insert casts to invoke the
    // correct overloads, and we can't perform data flow analysis until SSA is available. For
    // example, consider the snippet
    //     static void f(Object o) {}
    //     static void f(String s) {}
    //     static void g(String s) { f((Object)o); }
    // ...where the explicit cast to `Object` does not emit `checkcast` becuase it's an upcast, and
    // the only piece of information that specifies the correct overload is the method signature.
    pub descriptor: Str<'a>,
}

#[derive(Debug)]
pub enum CallKind<'a> {
    Static {
        class_or_interface: Str<'a>,
    },
    Method {
        class_or_interface: Str<'a>,
        object: Box<Expression<'a>>,
        is_special: bool,
    },
    Dynamic {
        bootstrap_method_attr: u16,
    },
}

impl Display for Call<'_> {
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
pub struct Arguments<'a>(pub Vec<Box<Expression<'a>>>);

impl Display for Arguments<'_> {
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
pub enum Type<'a> {
    /// {0}
    Reference(Str<'a>),
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
        }
    }
}

#[derive(Debug, Display)]
pub enum UnaryOp {
    /// -
    Neg,
}

#[derive(Debug, Display)]
pub enum VariableNamespace {
    /// slot
    Slot,
    /// stack
    Stack,
    /// tmp
    Temporary,
}

#[derive(Debug)]
pub struct Str<'a>(pub &'a MStr);

impl Display for Str<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.display())
    }
}
