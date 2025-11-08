use core::fmt;
use noak::{MStr, MString};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Str<'code>(pub &'code MStr);

impl fmt::Display for Str<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.display())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct String(pub MString);

impl fmt::Display for String {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0.display())
    }
}
