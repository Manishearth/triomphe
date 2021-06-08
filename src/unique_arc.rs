use alloc::{alloc::Layout, boxed::Box};
use core::convert::TryFrom;
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ops::{Deref, DerefMut};
use core::ptr::{self, NonNull};
use core::sync::atomic::AtomicUsize;

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

    /// Construct an uninitialized arc
    #[inline]
    pub fn new_uninit() -> UniqueArc<MaybeUninit<T>> {
        unsafe {
            let layout = Layout::new::<ArcInner<MaybeUninit<T>>>();
            let ptr = alloc::alloc::alloc(layout);
            let mut p = NonNull::new(ptr)
                .unwrap_or_else(|| alloc::alloc::handle_alloc_error(layout))
                .cast::<ArcInner<MaybeUninit<T>>>();
            ptr::write(&mut p.as_mut().count, AtomicUsize::new(1));

            UniqueArc(Arc {
                p,
                phantom: PhantomData,
            })
        }
    }

    /// Gets the inner value of the unique arc
    pub fn into_inner(this: Self) -> T {
        // Wrap the Arc in a `ManuallyDrop` so that its drop routine never runs
        let this = ManuallyDrop::new(this.0);
        debug_assert!(
            this.is_unique(),
            "attempted to call `.into_inner()` on a `UniqueArc` with a non-zero ref count",
        );

        // Safety: We have exclusive access to the inner data and the
        //         arc will not perform its drop routine since we've
        //         wrapped it in a `ManuallyDrop`
        unsafe { Box::from_raw(this.ptr()).data }
    }
}

impl<T: ?Sized> UniqueArc<T> {
    /// Convert to a shareable Arc<T> once we're done mutating it
    #[inline]
    pub fn shareable(self) -> Arc<T> {
        self.0
    }

    /// Creates a new [`UniqueArc`] from the given [`Arc`].
    ///
    /// An unchecked alternative to `Arc::try_unique()`
    ///
    /// # Safety
    ///
    /// The given `Arc` must have a reference count of exactly one
    ///
    pub(crate) unsafe fn from_arc(arc: Arc<T>) -> Self {
        debug_assert_eq!(Arc::count(&arc), 1);
        Self(arc)
    }
}

impl<T> UniqueArc<MaybeUninit<T>> {
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
            p: ManuallyDrop::new(this).0.p.cast(),
            phantom: PhantomData,
        })
    }
}

impl<T: ?Sized> TryFrom<Arc<T>> for UniqueArc<T> {
    type Error = Arc<T>;

    fn try_from(arc: Arc<T>) -> Result<Self, Self::Error> {
        Arc::try_unique(arc)
    }
}

impl<T: ?Sized> Deref for UniqueArc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &*self.0
    }
}

impl<T: ?Sized> DerefMut for UniqueArc<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        // We know this to be uniquely owned
        unsafe { &mut (*self.0.ptr()).data }
    }
}

// Safety:
// This leverages the correctness of Arc's CoerciblePtr impl. Additionally, we must ensure that
// this can not be used to violate the safety invariants of UniqueArc, which require that we can not
// duplicate the Arc, such that replace_ptr returns a valid instance. This holds since it consumes
// a unique owner of the contained ArcInner.
#[cfg(feature = "unsize")]
unsafe impl<T, U: ?Sized> unsize::CoerciblePtr<U> for UniqueArc<T> {
    type Pointee = T;
    type Output = UniqueArc<U>;

    fn as_sized_ptr(&mut self) -> *mut T {
        // Dispatch to the contained field.
        unsize::CoerciblePtr::<U>::as_sized_ptr(&mut self.0)
    }

    unsafe fn replace_ptr(self, new: *mut U) -> UniqueArc<U> {
        // Dispatch to the contained field, work around conflict of destructuring and Drop.
        let inner = ManuallyDrop::new(self);
        UniqueArc(ptr::read(&inner.0).replace_ptr(new))
    }
}

#[cfg(test)]
mod tests {
    use crate::{Arc, UniqueArc};
    use core::convert::TryFrom;

    #[test]
    fn unique_into_inner() {
        let unique = UniqueArc::new(10u64);
        assert_eq!(UniqueArc::into_inner(unique), 10);
    }

    #[test]
    fn try_from_arc() {
        let x = Arc::new(10_000);
        let y = x.clone();

        assert!(UniqueArc::try_from(x).is_err());
        assert_eq!(
            UniqueArc::into_inner(UniqueArc::try_from(y).unwrap()),
            10_000,
        );
    }
}
