use super::{DebugIr, Expression, Variable, VariableName};
use alloc::alloc;
use core::cell::Cell;
use core::fmt::{self, Display};
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ops::{Index, IndexMut};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);

// We want `last_id` at the start for performance and code size. Padding so that the start of the
// virtual non-biased chunk array is right at the beginning of the arena to avoid 3-operand lea.
#[repr(C)]
pub struct Arena<'code> {
    last_id: Cell<u32>,
    _padding: MaybeUninit<[u8; 5 * size_of::<usize>() - 4]>,
    chunks: [Cell<*mut Expression<'code>>; 27],
}

impl<'code> Arena<'code> {
    pub const fn new() -> Self {
        Self {
            last_id: Cell::new(31),
            _padding: MaybeUninit::uninit(),
            chunks: [const { Cell::new(core::ptr::without_provenance_mut(usize::MAX)) }; 27],
        }
    }

    pub fn capacity(&self) -> u32 {
        self.last_id.get() + 1
    }

    #[inline]
    pub fn alloc(&self, expr: Expression<'code>) -> ExprId {
        self.alloc_with(|_| expr)
    }

    #[inline]
    pub fn alloc_with<Cb: FnOnce(ExprId) -> Expression<'code>>(&self, cb: Cb) -> ExprId {
        let last_id = self.last_id.get();
        let id = last_id.wrapping_add(1);
        let mut cb = ManuallyDrop::new(cb);
        if last_id & id == 0 {
            let drop_cb = unsafe {
                core::mem::transmute::<unsafe fn(*mut Cb), unsafe fn(*mut ())>(
                    core::ptr::drop_in_place::<Cb>,
                )
            };
            unsafe {
                self.allocate_new_chunk(drop_cb, (&raw mut cb).cast());
            }
        }
        let cb = ManuallyDrop::into_inner(cb);
        let value = cb(ExprId(id));
        // If `cb` calls `alloc_with` recursively, this would overwrite an already existing value
        // without invalidating references to it, which can cause UAF. (Note that the fact that we
        // don't run the destructor in this case is irrelevant, since this can e.g. change the
        // active `enum` variant.) Assert that no new element has appeared. For simple enough `cb`s,
        // this should be optimized out.
        assert!(self.last_id.get() == last_id, "alloc_with is not reentrant");
        unsafe {
            self.get_raw_unchecked(ExprId(id)).write(value);
        }
        self.last_id.set(id);
        ExprId(id)
    }

    #[cold]
    unsafe fn allocate_new_chunk(&self, drop_cb: unsafe fn(*mut ()), drop_arg: *mut ()) {
        let id = self.last_id.get() + 1;
        if id == i32::MIN as u32 {
            unsafe {
                drop_cb(drop_arg);
            }
            panic!("failed to allocate expression");
        }
        unsafe {
            core::hint::assert_unchecked(id >= 32);
        }
        let chunk_id = id.ilog2();
        if self.chunks[chunk_id as usize - 5].get().addr() != usize::MAX {
            // Chunk already allocated, this can happen if `cb` panics on the first element of
            // a chunk.
            return;
        }
        let layout = Self::get_chunk_layout(chunk_id);
        let ptr: *mut Expression<'code> = unsafe { alloc::alloc(layout) }.cast();
        if ptr.is_null() {
            unsafe {
                drop_cb(drop_arg);
            }
            alloc::handle_alloc_error(layout);
        }
        self.chunks[chunk_id as usize - 5].set(ptr.wrapping_byte_sub(layout.size()));
    }

    fn get_chunk_layout(chunk_id: u32) -> alloc::Layout {
        let size = 1usize << chunk_id;
        assert!(size != 0);
        alloc::Layout::array::<Expression<'code>>(size)
            .expect("cannot allocate this many expressions")
            .align_to(2)
            .expect("cannot allocate this many expressions")
    }

    fn get_raw(&self, id: ExprId) -> *mut Expression<'code> {
        assert!(
            id.0 >= 32 && id.0 <= self.last_id.get(),
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

    pub fn var(&self, var: Variable) -> ExprId {
        self.alloc(Expression::Variable(var))
    }

    pub fn var_name(&self, name: VariableName) -> Variable {
        let version = self.alloc_with(|version| Expression::Variable(Variable { name, version }));
        Variable { name, version }
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

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut Expression<'code>> {
        let mut current_id = 32;
        let end_id = self.last_id.get() + 1;
        let mut chunk_ptr = core::ptr::null_mut();
        core::iter::from_fn(move || {
            if current_id == end_id {
                return None;
            }
            if current_id & (current_id - 1) == 0 {
                unsafe {
                    core::hint::assert_unchecked(current_id >= 32);
                }
                chunk_ptr = self.chunks[current_id.ilog2() as usize - 5].get();
            }
            let expr_ptr = chunk_ptr.wrapping_add(current_id as usize);
            current_id += 1;
            Some(unsafe { &mut *expr_ptr })
        })
    }

    pub fn swap(&mut self, a: ExprId, b: ExprId) {
        // `ptr::swap` handles overlapping regions.
        unsafe {
            core::ptr::swap(self.get_raw(a), self.get_raw(b));
        }
    }
}

impl<'code> Drop for Arena<'code> {
    fn drop(&mut self) {
        for chunk_id in 5..32 {
            let mut ptr = self.chunks[chunk_id as usize - 5].get();
            if ptr.addr() == usize::MAX {
                break;
            }
            ptr = ptr.wrapping_add(1 << chunk_id);

            unsafe {
                core::ptr::drop_in_place(core::ptr::slice_from_raw_parts_mut(
                    ptr,
                    (1 << chunk_id).min(self.last_id.get() + 1 - (1 << chunk_id)) as usize,
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
