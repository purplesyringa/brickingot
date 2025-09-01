use super::BasicStatement;
use crate::ast::{CallKind, ExprId, Expression};

// This iterates only over direct subexpressions, not recursively. The subexpressions are yielded in
// evaluation order.
//
// The implementation is a little ugly because we want the return type to be the same regardless of
// statement kind. We could take a callback, but then we'd have no way to enable iteration in
// reverse order.

type StmtIter = core::iter::Chain<core::option::IntoIter<ExprId>, core::option::IntoIter<ExprId>>;

impl BasicStatement {
    pub fn subexprs(&self) -> StmtIter {
        let (a, b): (Option<ExprId>, Option<ExprId>) = match self {
            Self::Assign { target, value } => (Some(*target), Some(*value)),

            Self::Return { value: expr }
            | Self::Calculate(expr)
            | Self::Throw { exception: expr }
            | Self::MonitorEnter { object: expr }
            | Self::MonitorExit { object: expr } => (Some(*expr), None),

            Self::ReturnVoid => (None, None),
        };

        a.into_iter().chain(b)
    }

    pub fn subexprs_from_single(expr_id: ExprId) -> StmtIter {
        Some(expr_id).into_iter().chain(None)
    }
}

impl Expression<'_> {
    pub fn subexprs(&self) -> impl DoubleEndedIterator<Item = ExprId> {
        let (a, b): (Option<ExprId>, &[ExprId]) = match self {
            Self::ArrayLength { array: expr }
            | Self::InstanceOf { object: expr, .. }
            | Self::CastReference { object: expr, .. }
            | Self::CastPrimitive { value: expr, .. }
            | Self::UnaryOp { argument: expr, .. } => (Some(*expr), &[]),

            Self::ArrayElement { array: a, index: b } | Self::BinOp { lhs: a, rhs: b, .. } => {
                (Some(*a), core::slice::from_ref(b))
            }

            Self::NewArray { lengths, .. } => (None, lengths),

            Self::Field { object, .. } => (*object, &[]),

            Self::Call {
                kind, arguments, ..
            } => (
                match kind {
                    CallKind::Method { object, .. } => Some(*object),
                    CallKind::Static { .. } | CallKind::Dynamic { .. } => None,
                },
                arguments,
            ),

            Self::This
            | Self::Argument { .. }
            | Self::NewUninitialized { .. }
            | Self::Null
            | Self::Variable(_)
            | Self::Class(_)
            | Self::DynamicConst(_)
            | Self::ConstMethodHandle(_)
            | Self::ConstMethodType { .. }
            | Self::ConstByte(_)
            | Self::ConstShort(_)
            | Self::ConstInt(_)
            | Self::ConstLong(_)
            | Self::ConstFloat(_)
            | Self::ConstDouble(_)
            | Self::ConstString(_) => (None, &[]),
        };

        a.into_iter().chain(b.iter().copied())
    }
}
