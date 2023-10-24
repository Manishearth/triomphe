use core::mem;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::ptr;

use super::Arc;

/// A "borrowed `Arc`". This is a pointer to
/// a T that is known to have been allocated within an
/// `Arc`.
///
/// This is equivalent in guarantees to `&Arc<T>`, however it is
/// a bit more flexible. To obtain an `&Arc<T>` you must have
/// an `Arc<T>` instance somewhere pinned down until we're done with it.
/// It's also a direct pointer to `T`, so using this involves less pointer-chasing
///
/// However, C++ code may hand us refcounted things as pointers to T directly,
/// so we have to conjure up a temporary `Arc` on the stack each time. The
/// same happens for when the object is managed by a `OffsetArc`.
///
/// `ArcBorrow` lets us deal with borrows of known-refcounted objects
/// without needing to worry about where the `Arc<T>` is.
#[derive(Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct ArcBorrow<'a, T: ?Sized + 'a>(pub(crate) &'a T);

impl<'a, T> Copy for ArcBorrow<'a, T> {}
impl<'a, T> Clone for ArcBorrow<'a, T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> ArcBorrow<'a, T> {
    /// Clone this as an `Arc<T>`. This bumps the refcount.
    #[inline]
    pub fn clone_arc(&self) -> Arc<T> {
        let arc = unsafe { Arc::from_raw(self.0) };
        // addref it!
        mem::forget(arc.clone());
        arc
    }

    /// For constructing from a reference known to be Arc-backed,
    /// e.g. if we obtain such a reference over FFI
    /// TODO: should from_ref be relaxed to unsized types? It can't be
    /// converted back to an Arc right now for unsized types.
    /// # Safety
    /// - The reference to `T` must have come from a Triomphe Arc, UniqueArc, or ArcBorrow.
    #[inline]
    pub unsafe fn from_ref(r: &'a T) -> Self {
        ArcBorrow(r)
    }

    /// Compare two `ArcBorrow`s via pointer equality. Will only return
    /// true if they come from the same allocation
    #[inline]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        ptr::eq(this.0 as *const T, other.0 as *const T)
    }

    /// Temporarily converts |self| into a bonafide Arc and exposes it to the
    /// provided callback. The refcount is not modified.
    #[inline]
    pub fn with_arc<F, U>(&self, f: F) -> U
    where
        F: FnOnce(&Arc<T>) -> U,
        T: 'static,
    {
        // Synthesize transient Arc, which never touches the refcount.
        let transient = unsafe { ManuallyDrop::new(Arc::from_raw(self.0)) };

        // Expose the transient Arc to the callback, which may clone it if it wants
        // and forward the result to the user
        f(&transient)
    }

    /// Similar to deref, but uses the lifetime |a| rather than the lifetime of
    /// self, which is incompatible with the signature of the Deref trait.
    #[inline]
    pub fn get(&self) -> &'a T {
        self.0
    }
}

impl<'a, T> Deref for ArcBorrow<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.0
    }
}

// Safety:
// This implementation must guarantee that it is sound to call replace_ptr with an unsized variant
// of the pointer retuned in `as_sized_ptr`. We leverage unsizing the contained reference. This
// continues to point to the data of an ArcInner. The reference count remains untouched which is
// correct since the number of owners did not change. This implies the returned instance fulfills
// its safety invariants.
#[cfg(feature = "unsize")]
unsafe impl<'lt, T: 'lt, U: ?Sized + 'lt> unsize::CoerciblePtr<U> for ArcBorrow<'lt, T> {
    type Pointee = T;
    type Output = ArcBorrow<'lt, U>;

    fn as_sized_ptr(&mut self) -> *mut T {
        // Returns a pointer to the inner data. We do not need to care about any particular
        // provenance here, only the pointer value, which we need to reconstruct the new pointer.
        self.0 as *const T as *mut T
    }

    unsafe fn replace_ptr(self, new: *mut U) -> ArcBorrow<'lt, U> {
        let inner = ManuallyDrop::new(self);
        // Safety: backed by the same Arc that backed `self`.
        ArcBorrow(inner.0.replace_ptr(new))
    }
}
