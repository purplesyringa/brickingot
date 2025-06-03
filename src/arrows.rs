#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ArrowKind {
    Jump { stmt_index: usize },
    Switch { stmt_index: usize, key: Option<i32> },
    Try { handler_index: usize },
    Dispatch { stmt_index: usize, selector: usize },
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Arrow {
    pub from: usize,
    pub to: usize,
    pub kind: ArrowKind,
}
