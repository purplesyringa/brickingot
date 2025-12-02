use super::{Arena, ExprId, GroupId, Str, Variable, Version};
use core::ops::Range;
use derive_deftly::define_derive_deftly;
use noak::reader::cpool::value::{Dynamic, MethodHandle};
use rustc_hash::FxHashMap;

pub fn compare<T: ?Sized + Isomorphic>(
    arena: &Arena<'_>,
    var_use_range: &FxHashMap<Version, Range<usize>>,
    x: &T,
    y: &T,
    x_root_range: Range<usize>,
) -> bool {
    Checker {
        arena,
        group_maps: FxHashMap::default(),
        var_maps: FxHashMap::default(),
        var_use_range,
        x_root_range,
    }
    .compare(x, y)
}

pub struct Checker<'a, 'code> {
    arena: &'a Arena<'code>,
    group_maps: FxHashMap<GroupId, GroupId>, // x -> y
    var_maps: FxHashMap<Version, Version>,   // x -> y
    var_use_range: &'a FxHashMap<Version, Range<usize>>,
    x_root_range: Range<usize>,
}

impl Checker<'_, '_> {
    pub fn define(&mut self, x: &GroupId, y: &GroupId) {
        self.group_maps.insert(*x, *y);
    }

    pub fn compare<T: ?Sized + Isomorphic>(&mut self, x: &T, y: &T) -> bool {
        x.compare(y, self)
    }
}

pub trait Isomorphic {
    fn compare(&self, other: &Self, checker: &mut Checker<'_, '_>) -> bool;
}

define_derive_deftly! {
    Isomorphic:

    impl<$tgens> crate::ast::isomorphism::Isomorphic for $ttype where $twheres {
        #[allow(unused)]
        fn compare(
            &self,
            other: &Self,
            checker: &mut crate::ast::isomorphism::Checker,
        ) -> bool {
            match (self, other) {
                $(
                    ($vpat, ${vpat fprefix=other_}) => {
                        $(
                            ${when fmeta(definition)}
                            checker.define($fpatname, $<other_ $fname>);
                        )
                        $(
                            ${when not(fmeta(ignore))}
                            ${when not(fmeta(definition))}
                            checker.compare($fpatname, $<other_ $fname>) &&
                        ) true
                    },
                )
                _ => false,
            }
        }
    }
}

pub(crate) use derive_deftly_template_Isomorphic;

macro_rules! via_eq {
    ($($ty:ty),* $(,)?) => {
        $(
            impl Isomorphic for $ty {
                fn compare(&self, other: &Self, _checker: &mut Checker<'_, '_>) -> bool {
                    self == other
                }
            }
        )*
    };
}

via_eq!(
    i8,
    i16,
    i32,
    i64,
    isize,
    u8,
    u16,
    u32,
    u64,
    usize,
    bool,
    Str<'_>,
    super::String,
    Dynamic<'_>,
    MethodHandle<'_>,
);

macro_rules! via_bits {
    ($($ty:ty),* $(,)?) => {
        $(
            impl Isomorphic for $ty {
                fn compare(&self, other: &Self, _checker: &mut Checker<'_, '_>) -> bool {
                    self.to_bits() == other.to_bits()
                }
            }
        )*
    };
}

via_bits!(f32, f64);

impl<T: Isomorphic> Isomorphic for [T] {
    fn compare(&self, other: &Self, checker: &mut Checker<'_, '_>) -> bool {
        self.len() == other.len() && self.iter().zip(other).all(|(x, y)| checker.compare(x, y))
    }
}

impl<T: Isomorphic> Isomorphic for Vec<T> {
    fn compare(&self, other: &Self, checker: &mut Checker<'_, '_>) -> bool {
        checker.compare::<[T]>(self.as_ref(), other.as_ref())
    }
}

impl<T: Isomorphic, const N: usize> Isomorphic for [T; N] {
    fn compare(&self, other: &Self, checker: &mut Checker<'_, '_>) -> bool {
        checker.compare::<[T]>(self.as_ref(), other.as_ref())
    }
}

impl<T: Isomorphic> Isomorphic for Option<T> {
    fn compare(&self, other: &Self, checker: &mut Checker<'_, '_>) -> bool {
        match (self, other) {
            (None, None) => true,
            (Some(x), Some(y)) => checker.compare(x, y),
            _ => false,
        }
    }
}

impl<T: Isomorphic, U: Isomorphic> Isomorphic for (T, U) {
    fn compare(&self, other: &Self, checker: &mut Checker<'_, '_>) -> bool {
        checker.compare(&self.0, &other.0) && checker.compare(&self.1, &other.1)
    }
}

impl Isomorphic for ExprId {
    fn compare(&self, other: &Self, checker: &mut Checker<'_, '_>) -> bool {
        checker.compare(&checker.arena[*self], &checker.arena[*other])
    }
}

impl Isomorphic for GroupId {
    fn compare(&self, other: &Self, checker: &mut Checker<'_, '_>) -> bool {
        checker.group_maps.get(self).copied().unwrap_or(*self) == *other
    }
}

impl Isomorphic for Variable {
    fn compare(&self, other: &Self, checker: &mut Checker<'_, '_>) -> bool {
        if self.version == other.version {
            return true;
        }

        // Can't assert full name equality because the `N` in all of `valueN`, `stackN`, and `slotN`
        // may reasonably differ.
        if self.name.namespace != other.name.namespace {
            return false;
        }

        let x_range = checker
            .var_use_range
            .get(&self.version)
            .expect("missing variable info");
        let x_used_only_within_x_root =
            checker.x_root_range.start <= x_range.start && x_range.end <= checker.x_root_range.end;
        if !x_used_only_within_x_root {
            // Free variables need to match exactly.
            return false;
        }

        *checker
            .var_maps
            .entry(self.version)
            .or_insert(other.version)
            == other.version
    }
}
