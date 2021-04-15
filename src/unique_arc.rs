use alloc::alloc::Layout;
use core::marker::PhantomData;
use core::mem;
use core::ops::{Deref, DerefMut};
use core::ptr;
use core::sync::atomic;

use super::{Arc, ArcInner};

/// An `Arc` that is known to be uniquely owned
///
/// When `Arc`s are constructed, they are known to be
/// uniquely owned. In such a case it is safe to mutate
/// the contents of the `Arc`. Normally, one would just handle
/// this by mutating the data on the stack before allocating the
/// `Arc`, however it's possible the data is large or unsized
/// and you need to heap-allocate it earlier in such a way
/// that it can be freely converted into a regular `Arc` once you're
/// done.
///
/// `UniqueArc` exists for this purpose, when constructed it performs
/// the same allocations necessary for an `Arc`, however it allows mutable access.
/// Once the mutation is finished, you can call `.shareable()` and get a regular `Arc`
/// out of it.
///
/// ```rust
/// # use triomphe::UniqueArc;
/// let data = [1, 2, 3, 4, 5];
/// let mut x = UniqueArc::new(data);
/// x[4] = 7; // mutate!
/// let y = x.shareable(); // y is an Arc<T>
/// ```
#[repr(transparent)]
pub struct UniqueArc<T: ?Sized>(Arc<T>);

impl<T> UniqueArc<T> {
    #[inline]
    /// Construct a new UniqueArc
    pub fn new(data: T) -> Self {
        UniqueArc(Arc::new(data))
    }

    #[inline]
    /// Convert to a shareable Arc<T> once we're done mutating it
    pub fn shareable(self) -> Arc<T> {
        self.0
    }

    /// Construct an uninitialized arc
    #[inline]
    pub fn new_uninit() -> UniqueArc<mem::MaybeUninit<T>> {
        unsafe {
            let layout = Layout::new::<ArcInner<mem::MaybeUninit<T>>>();
            let ptr = alloc::alloc::alloc(layout);
            let mut p = ptr::NonNull::new(ptr)
                .unwrap_or_else(|| alloc::alloc::handle_alloc_error(layout))
                .cast::<ArcInner<mem::MaybeUninit<T>>>();
            ptr::write(&mut p.as_mut().count, atomic::AtomicUsize::new(1));

            UniqueArc(Arc {
                p,
                phantom: PhantomData,
            })
        }
    }
}

impl<T> UniqueArc<mem::MaybeUninit<T>> {
    /// Convert to an initialized Arc.
    ///
    /// # Safety
    ///
    /// This function is equivalent to `MaybeUninit::assume_init` and has the
    /// same safety requirements. You are responsible for ensuring that the `T`
    /// has actually been initialized before calling this method.
    #[inline]
    pub unsafe fn assume_init(this: Self) -> UniqueArc<T> {
        UniqueArc(Arc {
            p: mem::ManuallyDrop::new(this).0.p.cast(),
            phantom: PhantomData,
        })
    }
}

impl<T> Deref for UniqueArc<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        &*self.0
    }
}

impl<T> DerefMut for UniqueArc<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // We know this to be uniquely owned
        unsafe { &mut (*self.0.ptr()).data }
    }
}

unsafe impl<T, U: ?Sized> unsize::CoerciblePtr<U> for UniqueArc<T> {
    type Pointee = T;
    type Output = UniqueArc<U>;
    fn as_sized_ptr(&mut self) -> *mut T {
        // Dispatch to the contained field.
        unsize::CoerciblePtr::<U>::as_sized_ptr(&mut self.0)
    }
    unsafe fn replace_ptr(self, new: *mut U) -> UniqueArc<U> {
        // Dispatch to the contained field, work around conflict of destructuring and Drop.
        let inner = mem::ManuallyDrop::new(self);
        UniqueArc(ptr::read(&inner.0).replace_ptr(new))
    }
}
