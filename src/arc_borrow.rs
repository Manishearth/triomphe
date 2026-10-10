use core::marker::PhantomData;
use core::mem;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::panic::{RefUnwindSafe, UnwindSafe};
use core::ptr::NonNull;

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
pub struct ArcBorrow<'a, T: ?Sized + 'a>(
    // Safety invariant: `0` is non-null, properly aligned, and points to the
    // initialized `data: T` field of a live `ArcInner<T>` allocation that stays
    // alive with strong count >= 1 for at least lifetime `'a`. `0` retains full
    // provenance over the entire `ArcInner<T>` allocation (never derived from a
    // narrowed `&T` reference).
    pub(crate) NonNull<T>,
    pub(crate) PhantomData<&'a T>,
);

// SAFETY:
// `ArcBorrow<'a, T>` is semantically equivalent to `&'a Arc<T>`: sending it to
// another thread permits reading `&'a T` (`T: Sync`) and cloning an owned
// `Arc<T>` that may later be dropped on that thread (`T: Send`).
unsafe impl<'a, T: ?Sized + Sync + Send> Send for ArcBorrow<'a, T> {}

// SAFETY:
// Sharing `&ArcBorrow<'a, T>` across threads permits copying `ArcBorrow<'a, T>`
// and either dereferencing `&'a T` (`T: Sync`) or cloning an `Arc<T>` (`T: Send`).
unsafe impl<'a, T: ?Sized + Sync + Send> Sync for ArcBorrow<'a, T> {}

impl<'a, T: RefUnwindSafe + ?Sized> UnwindSafe for ArcBorrow<'a, T> {}

impl<'a, T: ?Sized> Copy for ArcBorrow<'a, T> {}
impl<'a, T: ?Sized> Clone for ArcBorrow<'a, T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T: ?Sized> ArcBorrow<'a, T> {
    /// Clone this as an `Arc<T>`. This bumps the refcount.
    #[inline]
    pub fn clone_arc(&self) -> Arc<T> {
        // SAFETY:
        // By `ArcBorrow`'s field invariant, `self.0.as_ptr()` points to the
        // `data` field of a live `ArcInner<T>` with full allocation provenance.
        // Reconstructing `arc` via `Arc::from_raw` without incrementing the
        // reference count is balanced by immediately cloning `arc` (which
        // increments the strong count) and forgetting the clone via
        // `mem::forget` (which cannot panic), leaving the returned `Arc<T>`
        // with its own incremented strong reference.
        let arc = unsafe { Arc::from_raw(self.0.as_ptr()) };
        // addref it!
        mem::forget(arc.clone());
        arc
    }

    /// Returns the raw pointer to `T`.
    ///
    /// This pointer retains full provenance over the entire `ArcInner` allocation,
    /// and thus can be safely passed to [`Arc::from_raw`].
    #[inline]
    pub const fn to_raw(this: &Self) -> *const T {
        this.0.as_ptr()
    }

    /// For constructing from a pointer known to be Arc-backed,
    /// e.g. if we obtain such a pointer over FFI
    ///
    /// # Safety
    /// - The pointer to `T` must have come from a Triomphe `Arc`, `UniqueArc`, or `ArcBorrow`
    ///   that remains live (strong count >= 1) for the entire lifetime `'a`, and `T` must not
    ///   be mutably accessed for the duration of `'a`.
    /// - The pointer to `T` must have full provenance over the `Arc`, `UniqueArc`, or `ArcBorrow`,
    ///   in particular it must not have been derived from a `&T` reference, as references immediately
    ///   lose all provenance over the adjacent reference counts. Triomphe's `Arc` and `ArcBorrow`
    ///   offer direct APIs for obtaining such a pointer: [`Arc::as_ptr`], [`Arc::into_raw`], and [`ArcBorrow::to_raw`].
    #[inline]
    pub const unsafe fn from_ptr(ptr: *const T) -> Self {
        // SAFETY:
        // By this function's `# Safety` precondition, `ptr` came from a live
        // `Arc`, `UniqueArc`, or `ArcBorrow` (and is therefore non-null and
        // aligned for `T`), remains live for `'a`, and retains full provenance
        // over the `ArcInner<T>` allocation.
        unsafe { ArcBorrow(NonNull::new_unchecked(ptr as *mut T), PhantomData) }
    }

    /// Compare two `ArcBorrow`s via pointer equality. Will only return
    /// true if they come from the same allocation
    #[inline]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        core::ptr::addr_eq(this.0.as_ptr(), other.0.as_ptr())
    }

    /// The reference count of the underlying `Arc`.
    ///
    /// The number does not include borrowed pointers,
    /// or temporary `Arc` pointers created with functions like
    /// [`ArcBorrow::with_arc`].
    ///
    /// The function is called `strong_count` to mirror `std::sync::Arc::strong_count`,
    /// however `triomphe::Arc` does not support weak references.
    #[inline]
    pub fn strong_count(this: &Self) -> usize {
        Self::with_arc(this, |arc| Arc::strong_count(arc))
    }

    /// Temporarily converts |self| into a bonafide Arc and exposes it to the
    /// provided callback. The refcount is not modified.
    #[inline]
    pub fn with_arc<F, U>(&self, f: F) -> U
    where
        F: FnOnce(&Arc<T>) -> U,
    {
        // Synthesize transient Arc, which never touches the refcount.
        //
        // SAFETY:
        // By `ArcBorrow`'s field invariant, `self.0.as_ptr()` points to the
        // `data` field of a live `ArcInner<T>` with full allocation provenance
        // for at least `'a`. Wrapping the reconstructed `Arc<T>` in
        // `ManuallyDrop` ensures the borrowed strong reference count is not
        // decremented when `with_arc` returns or if `f` unwinds.
        let transient = unsafe { ManuallyDrop::new(Arc::from_raw(self.0.as_ptr())) };

        // Expose the transient Arc to the callback, which may clone it if it wants
        // and forward the result to the user
        f(&transient)
    }

    /// Similar to deref, but uses the lifetime |a| rather than the lifetime of
    /// self, which is incompatible with the signature of the Deref trait.
    #[inline]
    pub const fn get(&self) -> &'a T {
        // SAFETY:
        // By `ArcBorrow`'s field invariant, `self.0` is non-null, aligned, and
        // points to an initialized `T` in an `ArcInner<T>` allocation that
        // remains live and immutably shared for `'a`.
        unsafe { &*self.0.as_ptr() }
    }
}

impl<'a, T: ?Sized> Deref for ArcBorrow<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.get()
    }
}

// SAFETY:
// This implementation must guarantee that it is sound to call `replace_ptr` with an unsized variant
// of the pointer returned in `as_sized_ptr`. By `CoerciblePtr::replace_ptr`'s contract, `new` has
// the same address and provenance as `self.0` with unsized metadata for `U`. This continues to
// point to the `data` field of the same live `ArcInner` for `'lt`, and the reference count remains
// untouched since the number of owners did not change.
#[cfg(feature = "unsize")]
unsafe impl<'lt, T: 'lt, U: ?Sized + 'lt> unsize::CoerciblePtr<U> for ArcBorrow<'lt, T> {
    type Pointee = T;
    type Output = ArcBorrow<'lt, U>;

    fn as_sized_ptr(&mut self) -> *mut T {
        self.0.as_ptr()
    }

    unsafe fn replace_ptr(self, new: *mut U) -> ArcBorrow<'lt, U> {
        let inner = ManuallyDrop::new(self);
        // SAFETY:
        // By `CoerciblePtr::replace_ptr`'s contract, `new` is derived from
        // `self.as_sized_ptr()` via unsizing coercion, so it is non-null and
        // backed by the same live `ArcInner` allocation for `'lt` with full
        // provenance preserved.
        ArcBorrow(unsafe { inner.0.replace_ptr(new) }, PhantomData)
    }
}

#[test]
fn clone_arc_borrow() {
    let x = Arc::new(42);
    let b: ArcBorrow<'_, i32> = x.borrow_arc();
    let y = b.clone_arc();
    assert_eq!(x, y);
}

#[test]
fn clone_arc_borrow_str() {
    let x: Arc<str> = Arc::from("hello");
    let b: ArcBorrow<'_, str> = x.borrow_arc();
    let y: Arc<str> = b.clone_arc();
    assert_eq!(x, y);
    assert_eq!(&*b, "hello");
    assert!(ArcBorrow::ptr_eq(&b, &b));
}
