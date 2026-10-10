use core::fmt;
use core::hash::Hash;
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::panic::{RefUnwindSafe, UnwindSafe};
use core::ptr;

use super::{Arc, ArcBorrow};

/// An `Arc`, except it holds a pointer to the T instead of to the
/// entire ArcInner.
///
/// An `OffsetArc<T>` has the same layout and ABI as a non-null
/// `const T*` in C, and may be used in FFI function signatures.
///
/// ```text
///  Arc<T>    OffsetArc<T>
///   |          |
///   v          v
///  ---------------------
/// | RefCount | T (data) | [ArcInner<T>]
///  ---------------------
/// ```
///
/// This means that this is a direct pointer to
/// its contained data (and can be read from by both C++ and Rust),
/// but we can also convert it to a "regular" `Arc<T>` by removing the offset.
///
/// This is very useful if you have an Arc-containing struct shared between Rust and C++,
/// and wish for C++ to be able to read the data behind the `Arc` without incurring
/// an FFI call overhead.
#[repr(transparent)]
pub struct OffsetArc<T: ?Sized> {
    // Safety invariant: `ptr` is non-null, properly aligned, and points to the
    // initialized `data: T` field of a live `ArcInner<T>` heap allocation. It
    // retains full provenance over the entire `ArcInner<T>` allocation (as
    // obtained from `Arc::into_raw`), and this `OffsetArc` owns one strong
    // reference count on that `ArcInner<T>`.
    pub(crate) ptr: ptr::NonNull<T>,
    pub(crate) phantom: PhantomData<T>,
}

// SAFETY:
// `OffsetArc<T>` is semantically an `Arc<T>` stored at the `data` field offset:
// moving it across threads transfers ownership of one strong reference to the
// underlying `ArcInner<T>`, which may share `T` across threads (`T: Sync`) and
// drop `T` on the last thread (`T: Send`).
unsafe impl<T: ?Sized + Sync + Send> Send for OffsetArc<T> {}

// SAFETY:
// Sharing `&OffsetArc<T>` across threads only provides shared access (`&T`) to
// the payload (`T: Sync`), unless cloned and dropped on another thread (`T: Send`).
unsafe impl<T: ?Sized + Sync + Send> Sync for OffsetArc<T> {}

impl<T: ?Sized + RefUnwindSafe> UnwindSafe for OffsetArc<T> {}

impl<T: ?Sized> Deref for OffsetArc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // By the `OffsetArc::ptr` field invariant, `self.ptr` is non-null,
        // properly aligned, and points to an initialized `T` inside a live
        // `ArcInner<T>` allocation whose strong count is at least 1 for the
        // lifetime of `&self`. Shared access to `T` is sound because `Arc` only
        // permits mutation when uniquely owned (`make_mut` / `get_mut`).
        unsafe { &*self.ptr.as_ptr() }
    }
}

impl<T: ?Sized> Clone for OffsetArc<T> {
    #[inline]
    fn clone(&self) -> Self {
        Arc::into_raw_offset(self.clone_arc())
    }
}

impl<T: ?Sized> Drop for OffsetArc<T> {
    fn drop(&mut self) {
        let _ = Arc::from_raw_offset(OffsetArc {
            ptr: self.ptr,
            phantom: PhantomData,
        });
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for OffsetArc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized + PartialEq> PartialEq for OffsetArc<T> {
    fn eq(&self, other: &OffsetArc<T>) -> bool {
        *(*self) == *(*other)
    }

    #[allow(clippy::partialeq_ne_impl)]
    fn ne(&self, other: &OffsetArc<T>) -> bool {
        *(*self) != *(*other)
    }
}

impl<T: ?Sized + Eq> Eq for OffsetArc<T> {}

impl<T: ?Sized + PartialOrd> PartialOrd for OffsetArc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: ?Sized + Ord> Ord for OffsetArc<T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: ?Sized + Hash> Hash for OffsetArc<T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

impl<T> OffsetArc<T> {
    /// If uniquely owned, provide a mutable reference
    /// Else create a copy, and mutate that
    ///
    /// This is functionally the same thing as `Arc::make_mut`
    #[inline]
    pub fn make_mut(&mut self) -> &mut T
    where
        T: Clone,
    {
        // It is possible for `Arc::make_mut` to replace the Arc, or panic during
        // cloning or dropping the replaced old allocation.
        // We use a drop guard to ensure `self` is always updated to point to the current Arc,
        // even if a panic unwinds out of `Arc::make_mut`.
        struct DropGuard<'a, T> {
            // Safety invariant: `arc` is initialized and owns the active strong
            // reference originally moved out of `*this` (or its replacement
            // installed by `Arc::make_mut`) until `DropGuard::drop` takes it.
            arc: ManuallyDrop<Arc<T>>,
            this: &'a mut OffsetArc<T>,
        }

        impl<'a, T> Drop for DropGuard<'a, T> {
            fn drop(&mut self) {
                // SAFETY:
                // 1. `ManuallyDrop::take(&mut self.arc)`: By `DropGuard`'s
                //    invariant, `self.arc` is initialized and `take` is called
                //    only once here in `Drop::drop`. Even if `Arc::make_mut`
                //    unwinds during `T::clone` or during the old `Arc<T>`'s
                //    `Drop` in `*this = Arc::new(...)`, Rust place-assignment
                //    semantics move the old value out and write the new `Arc<T>`
                //    into `*this` before dropping the old temporary, so
                //    `self.arc` always holds a valid, live `Arc<T>`.
                // 2. `ptr::write(self.this, Arc::into_raw_offset(arc))`:
                //    `self.this` is a valid, aligned mutable reference whose
                //    previous `OffsetArc<T>` was logically moved out by
                //    `ptr::read` before constructing `DropGuard`. Writing the
                //    reconstructed `OffsetArc<T>` without dropping `*self.this`
                //    restores `*self.this`'s field invariant and transfers the
                //    strong reference back to `*self.this`.
                unsafe {
                    let arc = ManuallyDrop::take(&mut self.arc);
                    ptr::write(self.this, Arc::into_raw_offset(arc));
                }
            }
        }

        // SAFETY:
        // `self` is a valid, aligned reference to an initialized `OffsetArc<T>`.
        // `ptr::read(self)` bitwise-copies the `OffsetArc<T>` out so its strong
        // reference can be transferred to `Arc::from_raw_offset(this)`.
        // Postcondition: `*self` is logically moved-out until `guard` drops (both
        // on normal return and on unwind), so `*self` must not be read or
        // dropped before `guard` runs.
        let this = unsafe { ptr::read(self) };
        let mut guard = DropGuard {
            arc: ManuallyDrop::new(Arc::from_raw_offset(this)),
            this: self,
        };
        // Obtain the mutable reference. `Arc::make_mut` guarantees that
        // `guard.arc` is uniquely owned (strong count == 1) when it returns.
        let ret = Arc::make_mut(&mut *guard.arc) as *mut T;
        drop(guard);
        // SAFETY:
        // `ret` was obtained from `Arc::make_mut(&mut *guard.arc)`, so it is
        // non-null, aligned, and points to an initialized `T` in a uniquely
        // owned `ArcInner<T>` allocation. Dropping `guard` above converted that
        // same `Arc<T>` back into `*self` via `Arc::into_raw_offset` and
        // `ptr::write`, which only stores the data pointer into `self.ptr`
        // without deallocating, moving, or creating conflicting references to
        // the heap `T`. Because `self` is mutably borrowed for the caller's
        // lifetime, `&mut *ret` has exclusive access for that lifetime.
        unsafe { &mut *ret }
    }
}

impl<T: ?Sized> OffsetArc<T> {
    /// Temporarily converts |self| into a bonafide Arc and exposes it to the
    /// provided callback. The refcount is not modified.
    #[inline]
    pub fn with_arc<F, U>(&self, f: F) -> U
    where
        F: FnOnce(&Arc<T>) -> U,
    {
        // Synthesize transient Arc, which never touches the refcount of the ArcInner.
        //
        // SAFETY:
        // By `OffsetArc::ptr`'s field invariant, `self.ptr.as_ptr()` was created
        // by `Arc::into_raw` and retains full provenance over the live
        // `ArcInner<T>`. Wrapping the reconstructed `Arc<T>` in `ManuallyDrop`
        // ensures `Arc::from_raw` does not decrement the strong reference count
        // owned by `*self` when `with_arc` returns or if `f` unwinds.
        let transient = unsafe { ManuallyDrop::new(Arc::from_raw(self.ptr.as_ptr())) };

        // Expose the transient Arc to the callback, which may clone it if it wants
        // and forward the result to the user
        f(&transient)
    }

    /// Clone it as an `Arc`
    #[inline]
    pub fn clone_arc(&self) -> Arc<T> {
        OffsetArc::with_arc(self, |a| a.clone())
    }

    /// Produce a pointer to the data that can be converted back
    /// to an `Arc`
    #[inline]
    pub const fn borrow_arc(&self) -> ArcBorrow<'_, T> {
        ArcBorrow(self.ptr, PhantomData)
    }

    /// The reference count of this `Arc`.
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offset_arc_smoke() {
        let arc = Arc::new(42);
        let offset = Arc::into_raw_offset(arc);

        assert_eq!(*offset, 42);
        assert_eq!(OffsetArc::strong_count(&offset), 1);

        let offset2 = offset.clone();
        assert_eq!(OffsetArc::strong_count(&offset), 2);
        assert_eq!(offset, offset2);

        let regular_arc = offset2.clone_arc();
        assert_eq!(Arc::strong_count(&regular_arc), 3);
        drop(regular_arc);

        drop(offset2);
        assert_eq!(OffsetArc::strong_count(&offset), 1);

        let mut offset = offset;
        *offset.make_mut() = 99;
        assert_eq!(*offset, 99);

        let offset2 = offset.clone();
        *offset.make_mut() = 100;
        assert_eq!(*offset, 100);
        assert_eq!(*offset2, 99);
    }

    #[test]
    fn offset_arc_str() {
        let s: OffsetArc<str> = OffsetArc::from("hello world");
        assert_eq!(&*s, "hello world");
        assert_eq!(OffsetArc::strong_count(&s), 1);

        let b = s.borrow_arc();
        assert_eq!(&*b, "hello world");

        let s2 = s.clone();
        assert_eq!(OffsetArc::strong_count(&s), 2);
        assert_eq!(s, s2);
    }

    #[test]
    #[cfg(feature = "std")]
    fn safe_offset_arc_make_mut_reentrant_drop_panic_uaf() {
        use core::sync::atomic::{AtomicBool, Ordering};
        use std::panic::{catch_unwind, AssertUnwindSafe};
        use std::sync::{Arc as StdArc, Mutex};

        struct ReentrantClone {
            value: usize,
            sibling: StdArc<Mutex<Option<Arc<ReentrantClone>>>>,
            drop_panicked: StdArc<AtomicBool>,
        }

        impl Clone for ReentrantClone {
            fn clone(&self) -> Self {
                // `Arc::make_mut` observed two owners before calling us. Removing the
                // other owner here makes its transient owner the last one.
                drop(self.sibling.lock().unwrap().take());
                Self {
                    value: self.value,
                    sibling: self.sibling.clone(),
                    drop_panicked: self.drop_panicked.clone(),
                }
            }
        }

        impl Drop for ReentrantClone {
            fn drop(&mut self) {
                if !self.drop_panicked.swap(true, Ordering::SeqCst) {
                    panic!("old payload drop sentinel");
                }
            }
        }

        let sibling = StdArc::new(Mutex::new(None));
        let drop_panicked = StdArc::new(AtomicBool::new(false));
        let arc = Arc::new(ReentrantClone {
            value: 37,
            sibling: sibling.clone(),
            drop_panicked,
        });
        *sibling.lock().unwrap() = Some(arc.clone());
        let mut offset: OffsetArc<ReentrantClone> = Arc::into_raw_offset(arc);

        let result = catch_unwind(AssertUnwindSafe(|| {
            let _ = OffsetArc::make_mut(&mut offset);
        }));
        assert!(result.is_err());

        assert_eq!(offset.value, 37);
    }
}
