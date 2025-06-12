use crate::ast::Expression;
use alloc::alloc;
use core::cell::Cell;
use core::fmt::{self, Display};
use core::ops::{Index, IndexMut};

#[derive(Clone, Copy, Debug)]
pub struct ExprId(pub u32);

pub struct Arena<'code> {
    chunks: [Cell<*mut Expression<'code>>; 27],
    next_id: Cell<u32>,
}

impl<'code> Arena<'code> {
    pub fn new() -> Self {
        Self {
            chunks: [const { Cell::new(core::ptr::null_mut()) }; 27],
            next_id: Cell::new(32),
        }
    }

    #[inline]
    pub fn alloc(&self, expr: Expression<'code>) -> ExprId {
        self.alloc_with(|_| expr)
    }

    #[inline]
    pub fn alloc_with(&self, cb: impl FnOnce(ExprId) -> Expression<'code>) -> ExprId {
        let id = self.next_id.get();
        if id & (id - 1) == 0 && !unsafe { self.allocate_new_chunk() } {
            drop(cb);
            panic!("failed to allocate expression");
        }
        unsafe {
            self.get_raw_unchecked(ExprId(id)).write(cb(ExprId(id)));
        }
        self.next_id.set(id.wrapping_add(1));
        ExprId(id)
    }

    #[cold]
    unsafe fn allocate_new_chunk(&self) -> bool {
        let id = self.next_id.get();
        if id == 0 {
            return false;
        }
        unsafe {
            core::hint::assert_unchecked(id >= 32);
        }
        let chunk_id = id.ilog2();
        let layout = Self::get_chunk_layout(chunk_id);
        let ptr: *mut Expression<'code> = unsafe { alloc::alloc(layout) }.cast();
        if ptr.is_null() {
            // We can't call `alloc::handle_alloc_error(layout);` here because it may unwind, and
            // unwinding from `try_alloc` causes a cleanup pad for `expr` to be generated, and then
            // LLVM loses 20 IQ points and inserts a call to drop glue even if the active `expr`
            // variant is statically known not to require drop glue, and hence the `expr` variable
            // is allocated on the stack and then copied into heap instead of being directly
            // constructed on the heap. Sigh.
            return false;
        }
        self.chunks[chunk_id as usize - 5].set(ptr.wrapping_byte_sub(layout.size()));
        true
    }

    fn get_chunk_layout(chunk_id: u32) -> alloc::Layout {
        let size = 1usize << chunk_id;
        assert!(size != 0);
        alloc::Layout::array::<Expression<'code>>(size)
            .expect("cannot allocate this many expressions")
    }

    fn get_raw(&self, id: ExprId) -> *mut Expression<'code> {
        assert!(
            id.0 >= 32 && id.0 < self.next_id.get(),
            "out of bounds access",
        );
        unsafe { self.get_raw_unchecked(id) }
    }

    unsafe fn get_raw_unchecked(&self, id: ExprId) -> *mut Expression<'code> {
        unsafe {
            core::hint::assert_unchecked(id.0 >= 32);
        }
        let chunk_id = id.0.ilog2();
        self.chunks[chunk_id as usize - 5]
            .get()
            .wrapping_add(id.0 as usize)
    }

    pub fn int(&self, value: i32) -> ExprId {
        self.alloc(Expression::ConstInt(value))
    }

    pub fn null(&self) -> ExprId {
        self.alloc(Expression::Null)
    }

    pub fn debug<'a, T: DebugIr<'code> + ?Sized>(&'a self, value: &'a T) -> impl Display {
        struct IrDisplay<'a, 'code, T: ?Sized> {
            value: &'a T,
            arena: &'a Arena<'code>,
        }

        impl<'a, 'code, T: DebugIr<'code> + ?Sized> Display for IrDisplay<'a, 'code, T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                T::fmt(self.value, f, self.arena)
            }
        }

        IrDisplay { value, arena: self }
    }
}

impl<'code> Drop for Arena<'code> {
    fn drop(&mut self) {
        for chunk_id in 5..32 {
            if self.next_id.get() <= 1 << chunk_id {
                break;
            }

            let ptr = self.chunks[chunk_id as usize - 5]
                .get()
                .wrapping_add(1 << chunk_id);

            unsafe {
                core::ptr::drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    ptr,
                    (1 << chunk_id).min(self.next_id.get() - (1 << chunk_id)) as usize,
                ));
            }

            unsafe {
                alloc::dealloc(ptr.cast(), Self::get_chunk_layout(chunk_id));
            }
        }
    }
}

impl<'code> Index<ExprId> for Arena<'code> {
    type Output = Expression<'code>;

    fn index(&self, id: ExprId) -> &Self::Output {
        unsafe { &*self.get_raw(id) }
    }
}

impl<'code> IndexMut<ExprId> for Arena<'code> {
    fn index_mut(&mut self, id: ExprId) -> &mut Self::Output {
        unsafe { &mut *self.get_raw(id) }
    }
}

pub trait DebugIr<'code> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result;
}

impl<'code, T: DebugIr<'code> + ?Sized> DebugIr<'code> for &T {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        T::fmt(self, f, arena)
    }
}

impl<'code> DebugIr<'code> for ExprId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, arena: &Arena<'code>) -> fmt::Result {
        DebugIr::fmt(&arena[*self], f, arena)
    }
}
