use alloc::boxed::Box;
use core::alloc::Layout;
use core::borrow;
use core::cmp::Ordering;
use core::convert::From;
use core::ffi::c_void;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;
use core::mem;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ops::Deref;
use core::ptr;
use core::slice;
use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};
use core::{isize, usize};

#[cfg(feature = "std")]
use std::alloc::alloc;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "stable_deref_trait")]
use stable_deref_trait::{CloneStableDeref, StableDeref};

use crate::{abort, atomic, ArcBorrow, OffsetArc, UniqueArc};

/// A soft limit on the amount of references that may be made to an `Arc`.
///
/// Going above this limit will abort your program (although not
/// necessarily) at _exactly_ `MAX_REFCOUNT + 1` references.
const MAX_REFCOUNT: usize = (isize::MAX) as usize;

/// The object allocated by an Arc<T>
#[repr(C)]
pub(crate) struct ArcInner<T: ?Sized> {
    pub(crate) count: atomic::AtomicUsize,
    pub(crate) data: T,
}

#[repr(C)]
struct ArcInnerUninit<T: ?Sized> {
    count: MaybeUninit<atomic::AtomicUsize>,
    data: T,
}

unsafe impl<T: ?Sized + Sync + Send> Send for ArcInner<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for ArcInner<T> {}

/// An atomically reference counted shared pointer
///
/// See the documentation for [`Arc`] in the standard library. Unlike the
/// standard library `Arc`, this `Arc` does not support weak reference counting.
///
/// [`Arc`]: https://doc.rust-lang.org/stable/std/sync/struct.Arc.html
#[repr(transparent)]
pub struct Arc<T: ?Sized> {
    pub(crate) p: ptr::NonNull<ArcInner<T>>,
    pub(crate) phantom: PhantomData<T>,
}

unsafe impl<T: ?Sized + Sync + Send> Send for Arc<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Arc<T> {}

impl<T> Arc<T> {
    /// Construct an `Arc<T>`
    #[inline]
    pub fn new(data: T) -> Self {
        let ptr = Box::into_raw(Box::new(ArcInner {
            count: atomic::AtomicUsize::new(1),
            data,
        }));

        unsafe {
            Arc {
                p: ptr::NonNull::new_unchecked(ptr),
                phantom: PhantomData,
            }
        }
    }

    /// Convert the Arc<T> to a raw pointer, suitable for use across FFI
    ///
    /// Note: This returns a pointer to the data T, which is offset in the allocation.
    ///
    /// It is recommended to use OffsetArc for this.
    #[inline]
    pub fn into_raw(this: Self) -> *const T {
        let ptr = this.as_ptr();
        mem::forget(this);
        ptr
    }

    /// Returns the raw pointer.
    ///
    /// Same as into_raw except `self` isn't consumed.
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        unsafe { &((*self.ptr()).data) as *const _ }
    }

    /// Reconstruct the Arc<T> from a raw pointer obtained from into_raw()
    ///
    /// Note: This raw pointer will be offset in the allocation and must be preceded
    /// by the atomic count.
    ///
    /// It is recommended to use OffsetArc for this
    #[inline]
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        // To find the corresponding pointer to the `ArcInner` we need
        // to subtract the offset of the `data` field from the pointer.
        let ptr = (ptr as *const u8).sub(offset_of!(ArcInner<T>, data));
        Arc::from_raw_inner(ptr as *mut ArcInner<T>)
    }

    /// Produce a pointer to the data that can be converted back
    /// to an Arc. This is basically an `&Arc<T>`, without the extra indirection.
    /// It has the benefits of an `&T` but also knows about the underlying refcount
    /// and can be converted into more `Arc<T>`s if necessary.
    #[inline]
    pub fn borrow_arc(&self) -> ArcBorrow<'_, T> {
        ArcBorrow(&**self)
    }

    /// Temporarily converts |self| into a bonafide OffsetArc and exposes it to the
    /// provided callback. The refcount is not modified.
    #[inline(always)]
    pub fn with_raw_offset_arc<F, U>(&self, f: F) -> U
    where
        F: FnOnce(&OffsetArc<T>) -> U,
    {
        // Synthesize transient Arc, which never touches the refcount of the ArcInner.
        let transient = unsafe { ManuallyDrop::new(Arc::into_raw_offset(ptr::read(self))) };

        // Expose the transient Arc to the callback, which may clone it if it wants.
        let result = f(&transient);

        // Forget the transient Arc to leave the refcount untouched.
        mem::forget(transient);

        // Forward the result.
        result
    }

    /// Returns the address on the heap of the Arc itself -- not the T within it -- for memory
    /// reporting.
    pub fn heap_ptr(&self) -> *const c_void {
        self.p.as_ptr() as *const ArcInner<T> as *const c_void
    }

    /// Converts an `Arc` into a `OffsetArc`. This consumes the `Arc`, so the refcount
    /// is not modified.
    #[inline]
    pub fn into_raw_offset(a: Self) -> OffsetArc<T> {
        unsafe {
            OffsetArc {
                ptr: ptr::NonNull::new_unchecked(Arc::into_raw(a) as *mut T),
                phantom: PhantomData,
            }
        }
    }

    /// Converts a `OffsetArc` into an `Arc`. This consumes the `OffsetArc`, so the refcount
    /// is not modified.
    #[inline]
    pub fn from_raw_offset(a: OffsetArc<T>) -> Self {
        let ptr = a.ptr.as_ptr();
        mem::forget(a);
        unsafe { Arc::from_raw(ptr) }
    }

    /// Returns the inner value, if the [`Arc`] has exactly one strong reference.
    ///
    /// Otherwise, an [`Err`] is returned with the same [`Arc`] that was
    /// passed in.
    ///
    /// # Examples
    ///
    /// ```
    /// use triomphe::Arc;
    ///
    /// let x = Arc::new(3);
    /// assert_eq!(Arc::try_unwrap(x), Ok(3));
    ///
    /// let x = Arc::new(4);
    /// let _y = Arc::clone(&x);
    /// assert_eq!(*Arc::try_unwrap(x).unwrap_err(), 4);
    /// ```
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        Self::try_unique(this).map(UniqueArc::into_inner)
    }
}

impl<T: ?Sized> Arc<T> {
    /// Construct an `Arc` from an allocated `ArcInner`.
    /// # Safety
    /// The `ptr` must point to a valid instance, allocated by an `Arc`. The reference could will
    /// not be modified.
    unsafe fn from_raw_inner(ptr: *mut ArcInner<T>) -> Self {
        Arc {
            p: ptr::NonNull::new_unchecked(ptr),
            phantom: PhantomData,
        }
    }

    #[inline]
    pub(super) fn inner(&self) -> &ArcInner<T> {
        // This unsafety is ok because while this arc is alive we're guaranteed
        // that the inner pointer is valid. Furthermore, we know that the
        // `ArcInner` structure itself is `Sync` because the inner data is
        // `Sync` as well, so we're ok loaning out an immutable pointer to these
        // contents.
        unsafe { &*self.ptr() }
    }

    // Non-inlined part of `drop`. Just invokes the destructor.
    #[inline(never)]
    unsafe fn drop_slow(&mut self) {
        let _ = Box::from_raw(self.ptr());
    }

    /// Test pointer equality between the two Arcs, i.e. they must be the _same_
    /// allocation
    #[inline]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.ptr() == other.ptr()
    }

    pub(crate) fn ptr(&self) -> *mut ArcInner<T> {
        self.p.as_ptr()
    }
}

impl<T> Arc<MaybeUninit<T>> {
    /// Create an Arc contains an `MaybeUninit<T>`.
    pub fn new_uninit() -> Self {
        Arc::new(MaybeUninit::<T>::uninit())
    }

    /// Calls `MaybeUninit::write` on the value contained.
    pub fn write(&mut self, val: T) -> &mut T {
        unsafe {
            let ptr = (*self.ptr()).data.as_mut_ptr();
            ptr.write(val);
            &mut *ptr
        }
    }

    /// Obtain a mutable pointer to the stored `MaybeUninit<T>`.
    pub fn as_mut_ptr(&mut self) -> *mut MaybeUninit<T> {
        unsafe { &mut (*self.ptr()).data }
    }

    /// # Safety
    ///
    /// Must initialize all fields before calling this function.
    #[inline]
    pub unsafe fn assume_init(self) -> Arc<T> {
        Arc::from_raw_inner(ManuallyDrop::new(self).ptr().cast())
    }
}

#[cfg(feature = "std")]
impl<T> Arc<[MaybeUninit<T>]> {
    /// Create an Arc contains an array `[MaybeUninit<T>]` of `len`.
    pub fn new_uninit_slice(len: usize) -> Self {
        // layout should work as expected since ArcInner uses C representation.
        let layout = Layout::new::<atomic::AtomicUsize>();
        let array_layout = Layout::array::<MaybeUninit<T>>(len).unwrap();

        let (layout, _) = layout.extend(array_layout).unwrap();
        let layout = layout.pad_to_align();

        // Allocate and initialize ArcInner
        let ptr = unsafe {
            let ptr = alloc(layout);
            let slice = slice::from_raw_parts(ptr, len);

            let ptr = mem::transmute::<_, *mut ArcInnerUninit<[MaybeUninit<T>]>>(slice);
            (*ptr).count.as_mut_ptr().write(atomic::AtomicUsize::new(1));

            let ptr = mem::transmute::<_, *mut ArcInner<[MaybeUninit<T>]>>(ptr);
            debug_assert_eq!(mem::size_of_val(&*ptr), layout.size());
            ptr
        };

        Arc {
            p: ptr::NonNull::new(ptr).unwrap(),
            phantom: PhantomData,
        }
    }

    /// Obtain a mutable slice to the stored `[MaybeUninit<T>]`.
    pub fn as_mut_slice(&mut self) -> &mut [MaybeUninit<T>] {
        unsafe { &mut (*self.ptr()).data }
    }

    /// # Safety
    ///
    /// Must initialize all fields before calling this function.
    #[inline]
    pub unsafe fn assume_init(self) -> Arc<[T]> {
        Arc::from_raw_inner(ManuallyDrop::new(self).ptr() as _)
    }
}

impl<T: ?Sized> Clone for Arc<T> {
    #[inline]
    fn clone(&self) -> Self {
        // Using a relaxed ordering is alright here, as knowledge of the
        // original reference prevents other threads from erroneously deleting
        // the object.
        //
        // As explained in the [Boost documentation][1], Increasing the
        // reference counter can always be done with memory_order_relaxed: New
        // references to an object can only be formed from an existing
        // reference, and passing an existing reference from one thread to
        // another must already provide any required synchronization.
        //
        // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
        let old_size = self.inner().count.fetch_add(1, Relaxed);

        // However we need to guard against massive refcounts in case someone
        // is `mem::forget`ing Arcs. If we don't do this the count can overflow
        // and users will use-after free. We racily saturate to `isize::MAX` on
        // the assumption that there aren't ~2 billion threads incrementing
        // the reference count at once. This branch will never be taken in
        // any realistic program.
        //
        // We abort because such a program is incredibly degenerate, and we
        // don't care to support it.
        if old_size > MAX_REFCOUNT {
            abort();
        }

        unsafe {
            Arc {
                p: ptr::NonNull::new_unchecked(self.ptr()),
                phantom: PhantomData,
            }
        }
    }
}

impl<T: ?Sized> Deref for Arc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &self.inner().data
    }
}

impl<T: Clone + ?Sized> Arc<T> {
    /// Makes a mutable reference to the `Arc`, cloning if necessary
    ///
    /// This is functionally equivalent to [`Arc::make_mut`][mm] from the standard library.
    ///
    /// If this `Arc` is uniquely owned, `make_mut()` will provide a mutable
    /// reference to the contents. If not, `make_mut()` will create a _new_ `Arc`
    /// with a copy of the contents, update `this` to point to it, and provide
    /// a mutable reference to its contents.
    ///
    /// This is useful for implementing copy-on-write schemes where you wish to
    /// avoid copying things if your `Arc` is not shared.
    ///
    /// [mm]: https://doc.rust-lang.org/stable/std/sync/struct.Arc.html#method.make_mut
    #[inline]
    pub fn make_mut(this: &mut Self) -> &mut T {
        if !this.is_unique() {
            // Another pointer exists; clone
            *this = Arc::new((**this).clone());
        }

        unsafe {
            // This unsafety is ok because we're guaranteed that the pointer
            // returned is the *only* pointer that will ever be returned to T. Our
            // reference count is guaranteed to be 1 at this point, and we required
            // the Arc itself to be `mut`, so we're returning the only possible
            // reference to the inner data.
            &mut (*this.ptr()).data
        }
    }
}

impl<T: ?Sized> Arc<T> {
    /// Provides mutable access to the contents _if_ the `Arc` is uniquely owned.
    #[inline]
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        if this.is_unique() {
            unsafe {
                // See make_mut() for documentation of the threadsafety here.
                Some(&mut (*this.ptr()).data)
            }
        } else {
            None
        }
    }

    /// Whether or not the `Arc` is uniquely owned (is the refcount 1?).
    pub fn is_unique(&self) -> bool {
        // See the extensive discussion in [1] for why this needs to be Acquire.
        //
        // [1] https://github.com/servo/servo/issues/21186
        Self::count(self) == 1
    }

    /// Gets the number of [`Arc`] pointers to this allocation
    pub fn count(this: &Self) -> usize {
        this.inner().count.load(Acquire)
    }

    /// Returns a [`UniqueArc`] if the [`Arc`] has exactly one strong reference.
    ///
    /// Otherwise, an [`Err`] is returned with the same [`Arc`] that was
    /// passed in.
    ///
    /// # Examples
    ///
    /// ```
    /// use triomphe::{Arc, UniqueArc};
    ///
    /// let x = Arc::new(3);
    /// assert_eq!(UniqueArc::into_inner(Arc::try_unique(x).unwrap()), 3);
    ///
    /// let x = Arc::new(4);
    /// let _y = Arc::clone(&x);
    /// assert_eq!(
    ///     *Arc::try_unique(x).map(UniqueArc::into_inner).unwrap_err(),
    ///     4,
    /// );
    /// ```
    pub fn try_unique(this: Self) -> Result<UniqueArc<T>, Self> {
        if this.is_unique() {
            // Safety: The current arc is unique and making a `UniqueArc`
            //         from it is sound
            unsafe { Ok(UniqueArc::from_arc(this)) }
        } else {
            Err(this)
        }
    }
}

impl<T: ?Sized> Drop for Arc<T> {
    #[inline]
    fn drop(&mut self) {
        // Because `fetch_sub` is already atomic, we do not need to synchronize
        // with other threads unless we are going to delete the object.
        if self.inner().count.fetch_sub(1, Release) != 1 {
            return;
        }

        // FIXME(bholley): Use the updated comment when [2] is merged.
        //
        // This load is needed to prevent reordering of use of the data and
        // deletion of the data.  Because it is marked `Release`, the decreasing
        // of the reference count synchronizes with this `Acquire` load. This
        // means that use of the data happens before decreasing the reference
        // count, which happens before this load, which happens before the
        // deletion of the data.
        //
        // As explained in the [Boost documentation][1],
        //
        // > It is important to enforce any possible access to the object in one
        // > thread (through an existing reference) to *happen before* deleting
        // > the object in a different thread. This is achieved by a "release"
        // > operation after dropping a reference (any access to the object
        // > through this reference must obviously happened before), and an
        // > "acquire" operation before deleting the object.
        //
        // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
        // [2]: https://github.com/rust-lang/rust/pull/41714
        self.inner().count.load(Acquire);

        unsafe {
            self.drop_slow();
        }
    }
}

impl<T: ?Sized + PartialEq> PartialEq for Arc<T> {
    fn eq(&self, other: &Arc<T>) -> bool {
        Self::ptr_eq(self, other) || *(*self) == *(*other)
    }

    #[allow(clippy::partialeq_ne_impl)]
    fn ne(&self, other: &Arc<T>) -> bool {
        !Self::ptr_eq(self, other) && *(*self) != *(*other)
    }
}

impl<T: ?Sized + PartialOrd> PartialOrd for Arc<T> {
    fn partial_cmp(&self, other: &Arc<T>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }

    fn lt(&self, other: &Arc<T>) -> bool {
        *(*self) < *(*other)
    }

    fn le(&self, other: &Arc<T>) -> bool {
        *(*self) <= *(*other)
    }

    fn gt(&self, other: &Arc<T>) -> bool {
        *(*self) > *(*other)
    }

    fn ge(&self, other: &Arc<T>) -> bool {
        *(*self) >= *(*other)
    }
}

impl<T: ?Sized + Ord> Ord for Arc<T> {
    fn cmp(&self, other: &Arc<T>) -> Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: ?Sized + Eq> Eq for Arc<T> {}

impl<T: ?Sized + fmt::Display> fmt::Display for Arc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Arc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized> fmt::Pointer for Arc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Pointer::fmt(&self.ptr(), f)
    }
}

impl<T: Default> Default for Arc<T> {
    #[inline]
    fn default() -> Arc<T> {
        Arc::new(Default::default())
    }
}

impl<T: ?Sized + Hash> Hash for Arc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

impl<T> From<T> for Arc<T> {
    #[inline]
    fn from(t: T) -> Self {
        Arc::new(t)
    }
}

impl<T: ?Sized> borrow::Borrow<T> for Arc<T> {
    #[inline]
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized> AsRef<T> for Arc<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &**self
    }
}

#[cfg(feature = "stable_deref_trait")]
unsafe impl<T: ?Sized> StableDeref for Arc<T> {}
#[cfg(feature = "stable_deref_trait")]
unsafe impl<T: ?Sized> CloneStableDeref for Arc<T> {}

#[cfg(feature = "serde")]
impl<'de, T: Deserialize<'de>> Deserialize<'de> for Arc<T> {
    fn deserialize<D>(deserializer: D) -> Result<Arc<T>, D::Error>
    where
        D: ::serde::de::Deserializer<'de>,
    {
        T::deserialize(deserializer).map(Arc::new)
    }
}

#[cfg(feature = "serde")]
impl<T: Serialize> Serialize for Arc<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ::serde::ser::Serializer,
    {
        (**self).serialize(serializer)
    }
}

// Safety:
// This implementation must guarantee that it is sound to call replace_ptr with an unsized variant
// of the pointer retuned in `as_sized_ptr`. The basic property of Unsize coercion is that safety
// variants and layout is unaffected. The Arc does not rely on any other property of T. This makes
// any unsized ArcInner valid for being shared with the sized variant.
// This does _not_ mean that any T can be unsized into an U, but rather than if such unsizing is
// possible then it can be propagated into the Arc<T>.
#[cfg(feature = "unsize")]
unsafe impl<T, U: ?Sized> unsize::CoerciblePtr<U> for Arc<T> {
    type Pointee = T;
    type Output = Arc<U>;

    fn as_sized_ptr(&mut self) -> *mut T {
        // Returns a pointer to the complete inner. The unsizing itself won't care about the
        // pointer value and promises not to offset it.
        self.p.as_ptr() as *mut T
    }

    unsafe fn replace_ptr(self, new: *mut U) -> Arc<U> {
        // Fix the provenance by ensuring that of `self` is used.
        let inner = ManuallyDrop::new(self);
        let p = inner.p.as_ptr() as *mut T;
        // Safety: This points to an ArcInner of the previous self and holds shared ownership since
        // the old pointer never decremented the reference count. The caller upholds that `new` is
        // an unsized version of the previous ArcInner. This assumes that unsizing to the fat
        // pointer tag of an `ArcInner<U>` and `U` is isomorphic under a direct pointer cast since
        // in reality we unsized *mut T to *mut U at the address of the ArcInner. This is the case
        // for all currently envisioned unsized types where the tag of T and ArcInner<T> are simply
        // the same.
        Arc::from_raw_inner(p.replace_ptr(new) as *mut ArcInner<U>)
    }
}

#[cfg(test)]
mod tests {
    use crate::arc::Arc;
    use core::mem::MaybeUninit;
    #[cfg(feature = "unsize")]
    use unsize::{CoerceUnsize, Coercion};

    #[test]
    fn try_unwrap() {
        let x = Arc::new(100usize);
        let y = x.clone();

        // The count should be two so `try_unwrap()` should fail
        assert_eq!(Arc::count(&x), 2);
        assert!(Arc::try_unwrap(x).is_err());

        // Since `x` has now been dropped, the count should be 1
        // and `try_unwrap()` should succeed
        assert_eq!(Arc::count(&y), 1);
        assert_eq!(Arc::try_unwrap(y), Ok(100));
    }

    #[test]
    #[cfg(feature = "unsize")]
    fn coerce_to_slice() {
        let x = Arc::new([0u8; 4]);
        let y: Arc<[u8]> = x.clone().unsize(Coercion::to_slice());
        assert_eq!((*x).as_ptr(), (*y).as_ptr());
    }

    #[test]
    #[cfg(feature = "unsize")]
    fn coerce_to_dyn() {
        let x: Arc<_> = Arc::new(|| 42u32);
        let x: Arc<_> = x.unsize(Coercion::<_, dyn Fn() -> u32>::to_fn());
        assert_eq!((*x)(), 42);
    }

    #[test]
    fn maybeuninit() {
        let mut arc: Arc<MaybeUninit<_>> = Arc::new_uninit();
        arc.write(999);

        let arc = unsafe { arc.assume_init() };
        assert_eq!(*arc, 999);
    }

    #[test]
    #[cfg(feature = "std")]
    #[cfg_attr(miri, ignore)]
    fn maybeuninit_array() {
        let mut arc: Arc<[MaybeUninit<_>]> = Arc::new_uninit_slice(5);
        assert!(arc.is_unique());
        for (uninit, index) in arc.as_mut_slice().iter_mut().zip(0..5) {
            let ptr = uninit.as_mut_ptr();
            unsafe { core::ptr::write(ptr, index) };
        }

        let arc = unsafe { arc.assume_init() };
        assert!(arc.is_unique());
        // Using clone to that the layout generated in new_uninit_slice is compatible
        // with ArcInner.
        let arcs = [
            arc.clone(),
            arc.clone(),
            arc.clone(),
            arc.clone(),
            arc.clone(),
        ];
        assert_eq!(6, Arc::count(&arc));
        // If the layout is not compatible, then the data might be corrupted.
        assert_eq!(*arc, [0, 1, 2, 3, 4]);

        // Drop the arcs and check the count and the content to
        // make sure it isn't corrupted.
        drop(arcs);
        assert!(arc.is_unique());
        assert_eq!(*arc, [0, 1, 2, 3, 4]);
    }
}
