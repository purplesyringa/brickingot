use super::{Arena, DebugIr, ExprId, Str, isomorphism::derive_deftly_template_Isomorphic};
use core::fmt::{self, Display};
use core::hash::{Hash, Hasher};
use derive_deftly::Deftly;
use displaydoc::Display;
use noak::reader::cpool::value::{Dynamic, MethodHandle};

#[derive(Debug, Deftly)]
#[derive_deftly(Isomorphic)]
pub enum Expression<'code> {
    This,
    Argument {
        index: usize,
    },
    ArrayElement {
        array: ExprId,
        index: ExprId,
    },
    ArrayLength {
        array: ExprId,
    },
    NewArray {
        element_type: Type<'code>,
        lengths: Vec<ExprId>,
    },
    NewUninitialized {
        class: Str<'code>,
    },
    Null,
    Variable(Variable),
    Field {
        // `None` for static fields
        object: Option<ExprId>,
        class: Str<'code>,
        name: Str<'code>,
        // JVM bytecode allows fields with equal names but different types to co-exist, Java
        // doesn't. Decompiling such code correctly requires us to track types.
        descriptor: Str<'code>,
    },
    Class(Str<'code>),
    DynamicConst(Dynamic<'code>),
    ConstMethodHandle(MethodHandle<'code>),
    ConstMethodType {
        descriptor: Str<'code>,
    },
    ConstByte(i8),
    ConstShort(i16),
    ConstInt(i32),
    ConstLong(i64),
    ConstFloat(f32),
    ConstDouble(f64),
    ConstString(Str<'code>),
    InstanceOf {
        object: ExprId,
        class: Str<'code>,
    },
    CastReference {
        object: ExprId,
        class: Str<'code>,
    },
    CastPrimitive {
        value: ExprId,
        from: PrimitiveType,
        to: PrimitiveType,
    },
    BinOp {
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    UnaryOp {
        op: UnaryOp,
        argument: ExprId,
    },
    Call {
        method_name: Str<'code>,
        kind: CallKind<'code>,
        arguments: Vec<ExprId>,
        // We retain method descriptors until codegen because we may need to insert casts to invoke
        // the correct overloads, and we can't perform data flow analysis until SSA-like independent
        // variables have been established. For example, consider the snippet
        //     static void f(Object o) {}
        //     static void f(String s) {}
        //     static void g(String s) { f((Object)o); }
        // ...where the explicit cast to `Object` does not emit `checkcast` because it's an upcast,
        // and the only piece of information that specifies the correct overload is the method
        // signature.
        descriptor: Str<'code>,
    },
    Ternary {
        condition: ExprId,
        // This is typed weirdly due to the iteration implementation, which assumes that the
        // expressions have at most 2 child expressions or lists of expressions, whereas this would
        // have 3.
        branches: [ExprId; 2], // [if_true, if_false]
    },
    LogicalOp {
        op: LogicalOp,
        lhs: ExprId,
        rhs: ExprId,
    },
}

impl DebugIr for Expression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'_>) -> fmt::Result {
        match self {
            Self::This => write!(f, "this"),
            Self::Argument { index } => write!(f, "arg{index}"),
            Self::ArrayElement { array, index } => {
                write!(f, "({})[{}]", arena.debug(array), arena.debug(index))
            }
            Self::ArrayLength { array } => write!(f, "({}).length", arena.debug(array)),
            Self::NewArray {
                element_type,
                lengths,
            } => {
                write!(f, "new {element_type}")?;
                for len in lengths {
                    write!(f, "[{}]", arena.debug(len))?;
                }
                Ok(())
            }
            Self::NewUninitialized { class } => write!(f, "new uninitialized {class}"),
            Self::Null => write!(f, "null"),
            Self::Variable(var) => write!(f, "{var}"),
            Self::Field {
                object,
                class,
                name,
                descriptor,
            } => {
                if let Some(object) = object {
                    write!(f, "({}).", arena.debug(object))?;
                }
                write!(f, "{}::{}[{}]", class, name, descriptor)
            }
            Self::Class(name) => write!(f, "{name}.class"),
            Self::DynamicConst(dynamic) => write!(f, "{dynamic:?}"),
            Self::ConstMethodHandle(handle) => write!(f, "{handle:?}"),
            Self::ConstMethodType { descriptor } => write!(f, "MethodType({descriptor:?})"),
            Self::ConstByte(n) => write!(f, "{n}b"),
            Self::ConstShort(n) => write!(f, "{n}s"),
            Self::ConstInt(n) => write!(f, "{n}i"),
            Self::ConstLong(n) => write!(f, "{n}l"),
            Self::ConstFloat(n) => write!(f, "{n}f"),
            Self::ConstDouble(n) => write!(f, "{n}d"),
            Self::ConstString(value) => write!(f, "{value:?}"),
            Self::InstanceOf { object, class } => {
                write!(f, "({}) instanceof {class}", arena.debug(object))
            }
            Self::CastReference { object, class } => {
                write!(f, "({class})({})", arena.debug(object))
            }
            Self::CastPrimitive { value, from, to } => {
                write!(f, "({from} -> {to})({})", arena.debug(value))
            }
            Self::BinOp { op, lhs, rhs } => {
                write!(f, "({}) {op} ({})", arena.debug(lhs), arena.debug(rhs))
            }
            Self::UnaryOp { op, argument } => write!(f, "{op}({})", arena.debug(argument)),
            Self::Call {
                method_name,
                kind,
                arguments,
                descriptor,
            } => {
                match kind {
                    CallKind::Static { class_or_interface } => write!(f, "{class_or_interface}::")?,
                    CallKind::Method {
                        class_or_interface,
                        object,
                        is_special,
                    } => {
                        write!(f, "({}).", arena.debug(object))?;
                        if *is_special {
                            write!(f, "special ")?;
                        }
                        write!(f, "{class_or_interface}::")?;
                    }
                    CallKind::Dynamic {
                        bootstrap_method_attr,
                    } => write!(f, "indy #{bootstrap_method_attr} ")?,
                }
                write!(f, "{}[{}](", method_name, descriptor)?;
                if let Some(first_arg) = arguments.first() {
                    write!(f, "{}", arena.debug(first_arg))?;
                    for arg in &arguments[1..] {
                        write!(f, ", {}", arena.debug(arg))?;
                    }
                }
                write!(f, ")")
            }
            Self::Ternary {
                condition,
                branches: [if_then, if_else],
            } => write!(
                f,
                "({}) ? ({}) : ({})",
                arena.debug(condition),
                arena.debug(if_then),
                arena.debug(if_else)
            ),
            Self::LogicalOp { op, lhs, rhs } => {
                write!(f, "({}) {op} ({})", arena.debug(lhs), arena.debug(rhs))
            }
        }
    }
}

#[derive(Debug, Deftly)]
#[derive_deftly(Isomorphic)]
pub enum CallKind<'code> {
    Static {
        class_or_interface: Str<'code>,
    },
    Method {
        class_or_interface: Str<'code>,
        object: ExprId,
        is_special: bool,
    },
    Dynamic {
        bootstrap_method_attr: u16,
    },
}

#[derive(Debug, Display, Deftly)]
#[derive_deftly(Isomorphic)]
pub enum Type<'code> {
    /// {0}
    Reference(Str<'code>),
    /// {0}
    Primitive(PrimitiveType),
}

#[derive(Clone, Copy, Debug, Display, Deftly)]
#[derive_deftly(Isomorphic)]
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

#[derive(Debug, Deftly)]
#[derive_deftly(Isomorphic)]
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

#[derive(Debug, Deftly, Display)]
#[derive_deftly(Isomorphic)]
pub enum UnaryOp {
    /// -
    Neg,
    /// !
    Not,
}

#[derive(Debug, Deftly, Display)]
#[derive_deftly(Isomorphic)]
pub enum LogicalOp {
    /// &&
    And,
    /// ||
    Or,
}

#[derive(Clone, Copy, Debug)]
pub struct Variable {
    pub name: VariableName,
    pub version: Version,
}

// Variables with equal versions are guaranteed to have the same name, so only versions need to be
// compared.
impl PartialEq for Variable {
    fn eq(&self, rhs: &Variable) -> bool {
        self.version == rhs.version
    }
}
impl Eq for Variable {}
impl Hash for Variable {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.version.hash(hasher);
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", self.name, self.version)
    }
}

/// {namespace}{id}
#[derive(Clone, Copy, Debug, Display, Hash, PartialEq, Eq)]
pub struct VariableName {
    pub id: usize,
    pub namespace: VariableNamespace,
}

#[derive(Clone, Copy, Debug, Display, Hash, PartialEq, Eq)]
pub enum VariableNamespace {
    /// slot
    Slot,
    /// stack
    Stack,
    /// value
    Value,
    /// selector
    Selector,
    /// context
    Context,
}

#[derive(Clone, Copy, Debug, Display, Hash, PartialEq, Eq)]
pub struct Version(pub u32);

impl Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0 - 32)
    }
}

/// A helper macro for creating instances of `VariableName` and `Variable`.
#[macro_export]
macro_rules! var {
    (@impl $namespace:tt $id:expr) => {
        $crate::ast::VariableName {
            id: $id,
            namespace: $crate::ast::VariableNamespace::$namespace,
        }
    };

    (slot $n:expr) => { $crate::var!(@impl Slot $n) };
    (stack $n:expr) => { $crate::var!(@impl Stack $n) };
    (stack0) => { $crate::var!(@impl Stack 0) };
    (value $n:expr) => { $crate::var!(@impl Value $n) };
    (selector0) => { $crate::var!(@impl Selector 0) };
    (context0) => { $crate::var!(@impl Context 0) };

    (@muncher [$($parsed:tt)*] v $version:expr) => {
        $crate::ast::Variable {
            name: $crate::var!($($parsed)*),
            version: $version,
        }
    };
    (@muncher [$($parsed:tt)*]) => { $($parsed)* };
    (@muncher [$($parsed:tt)*] $head:tt $($tail:tt)*) => {
        $crate::var!(@muncher [$($parsed)* $head] $($tail)*)
    };
    ($($tt:tt)*) => { $crate::var!(@muncher [] $($tt)*) };
}
