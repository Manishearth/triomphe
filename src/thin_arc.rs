use core::cmp::Ordering;
use core::ffi::c_void;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::iter::{ExactSizeIterator, Iterator};
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Deref;
use core::ptr;
use core::usize;

use super::{Arc, ArcInner, HeaderSliceWithLength, HeaderWithLength};

/// A "thin" `Arc` containing dynamically sized data
///
/// This is functionally equivalent to `Arc<(H, [T])>`
///
/// When you create an `Arc` containing a dynamically sized type
/// like `HeaderSlice<H, [T]>`, the `Arc` is represented on the stack
/// as a "fat pointer", where the length of the slice is stored
/// alongside the `Arc`'s pointer. In some situations you may wish to
/// have a thin pointer instead, perhaps for FFI compatibility
/// or space efficiency.
///
/// Note that we use `[T; 0]` in order to have the right alignment for `T`.
///
/// `ThinArc` solves this by storing the length in the allocation itself,
/// via `HeaderSliceWithLength`.
#[repr(transparent)]
pub struct ThinArc<H, T> {
    ptr: ptr::NonNull<ArcInner<HeaderSliceWithLength<H, [T; 0]>>>,
    phantom: PhantomData<(H, T)>,
}

unsafe impl<H: Sync + Send, T: Sync + Send> Send for ThinArc<H, T> {}
unsafe impl<H: Sync + Send, T: Sync + Send> Sync for ThinArc<H, T> {}

// Synthesize a fat pointer from a thin pointer.
//
// See the comment around the analogous operation in from_header_and_iter.
#[inline]
fn thin_to_thick<H, T>(
    thin: *mut ArcInner<HeaderSliceWithLength<H, [T; 0]>>,
) -> *mut ArcInner<HeaderSliceWithLength<H, [T]>> {
    let len = unsafe { (*thin).data.header.length };
    let fake_slice = ptr::slice_from_raw_parts_mut(thin as *mut T, len);

    fake_slice as *mut ArcInner<HeaderSliceWithLength<H, [T]>>
}

impl<H, T> ThinArc<H, T> {
    /// Temporarily converts |self| into a bonafide Arc and exposes it to the
    /// provided callback. The refcount is not modified.
    #[inline]
    pub fn with_arc<F, U>(&self, f: F) -> U
    where
        F: FnOnce(&Arc<HeaderSliceWithLength<H, [T]>>) -> U,
    {
        // Synthesize transient Arc, which never touches the refcount of the ArcInner.
        let transient = unsafe {
            ManuallyDrop::new(Arc {
                p: ptr::NonNull::new_unchecked(thin_to_thick(self.ptr.as_ptr())),
                phantom: PhantomData,
            })
        };

        // Expose the transient Arc to the callback, which may clone it if it wants
        // and forward the result to the user
        f(&transient)
    }

    /// Creates a `ThinArc` for a HeaderSlice using the given header struct and
    /// iterator to generate the slice.
    pub fn from_header_and_iter<I>(header: H, items: I) -> Self
    where
        I: Iterator<Item = T> + ExactSizeIterator,
    {
        let header = HeaderWithLength::new(header, items.len());
        Arc::into_thin(Arc::from_header_and_iter(header, items))
    }

    /// Creates a `ThinArc` for a HeaderSlice using the given header struct and
    /// a slice to copy.
    pub fn from_header_and_slice(header: H, items: &[T]) -> Self
    where
        T: Copy,
    {
        let header = HeaderWithLength::new(header, items.len());
        Arc::into_thin(Arc::from_header_and_slice(header, items))
    }

    /// Returns the address on the heap of the ThinArc itself -- not the T
    /// within it -- for memory reporting.
    #[inline]
    pub fn ptr(&self) -> *const c_void {
        self.ptr.as_ptr() as *const ArcInner<T> as *const c_void
    }

    /// Returns the address on the heap of the Arc itself -- not the T within it -- for memory
    /// reporting.
    #[inline]
    pub fn heap_ptr(&self) -> *const c_void {
        self.ptr()
    }

    /// # Safety
    ///
    /// Constructs an ThinArc from a raw pointer.
    ///
    /// The raw pointer must have been previously returned by a call to
    /// ThinArc::into_raw.
    ///
    /// The user of from_raw has to make sure a specific value of T is only dropped once.
    ///
    /// This function is unsafe because improper use may lead to memory unsafety,
    /// even if the returned ThinArc is never accessed.
    #[inline]
    pub unsafe fn from_raw(ptr: *const c_void) -> Self {
        Self {
            ptr: ptr::NonNull::new_unchecked(ptr as *mut c_void).cast(),
            phantom: PhantomData,
        }
    }

    /// Consume ThinArc and returned the wrapped pointer.
    #[inline]
    pub fn into_raw(self) -> *const c_void {
        let this = ManuallyDrop::new(self);
        this.ptr.cast().as_ptr()
    }

    /// Provides a raw pointer to the data.
    /// The counts are not affected in any way and the ThinArc is not consumed.
    /// The pointer is valid for as long as there are strong counts in the ThinArc.
    #[inline]
    pub fn as_ptr(&self) -> *const c_void {
        self.ptr()
    }
}

impl<H, T> Deref for ThinArc<H, T> {
    type Target = HeaderSliceWithLength<H, [T]>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { &(*thin_to_thick(self.ptr.as_ptr())).data }
    }
}

impl<H, T> Clone for ThinArc<H, T> {
    #[inline]
    fn clone(&self) -> Self {
        ThinArc::with_arc(self, |a| {
            // Safety: `a` isn't mutable thus the header length remains valid
            unsafe { Arc::into_thin_unchecked(a.clone()) }
        })
    }
}

impl<H, T> Drop for ThinArc<H, T> {
    #[inline]
    fn drop(&mut self) {
        let _ = Arc::from_thin(ThinArc {
            ptr: self.ptr,
            phantom: PhantomData,
        });
    }
}

impl<H, T> Arc<HeaderSliceWithLength<H, [T]>> {
    /// Converts an `Arc` into a `ThinArc`. This consumes the `Arc`, so the refcount
    /// is not modified.
    ///
    /// # Safety
    /// Assumes that the header length matches the slice length.
    #[inline]
    unsafe fn into_thin_unchecked(a: Self) -> ThinArc<H, T> {
        let a = ManuallyDrop::new(a);
        debug_assert_eq!(
            a.header.length,
            a.slice.len(),
            "Length needs to be correct for ThinArc to work"
        );
        let fat_ptr: *mut ArcInner<HeaderSliceWithLength<H, [T]>> = a.ptr();
        let thin_ptr = fat_ptr as *mut [usize] as *mut usize;
        ThinArc {
            ptr: unsafe {
                ptr::NonNull::new_unchecked(
                    thin_ptr as *mut ArcInner<HeaderSliceWithLength<H, [T; 0]>>,
                )
            },
            phantom: PhantomData,
        }
    }

    /// Converts an `Arc` into a `ThinArc`. This consumes the `Arc`, so the refcount
    /// is not modified.
    #[inline]
    pub fn into_thin(a: Self) -> ThinArc<H, T> {
        assert_eq!(
            a.header.length,
            a.slice.len(),
            "Length needs to be correct for ThinArc to work"
        );
        unsafe { Self::into_thin_unchecked(a) }
    }

    /// Converts a `ThinArc` into an `Arc`. This consumes the `ThinArc`, so the refcount
    /// is not modified.
    #[inline]
    pub fn from_thin(a: ThinArc<H, T>) -> Self {
        let a = ManuallyDrop::new(a);
        let ptr = thin_to_thick(a.ptr.as_ptr());
        unsafe {
            Arc {
                p: ptr::NonNull::new_unchecked(ptr),
                phantom: PhantomData,
            }
        }
    }
}

impl<H: PartialEq, T: PartialEq> PartialEq for ThinArc<H, T> {
    #[inline]
    fn eq(&self, other: &ThinArc<H, T>) -> bool {
        ThinArc::with_arc(self, |a| ThinArc::with_arc(other, |b| *a == *b))
    }
}

impl<H: Eq, T: Eq> Eq for ThinArc<H, T> {}

impl<H: PartialOrd, T: PartialOrd> PartialOrd for ThinArc<H, T> {
    #[inline]
    fn partial_cmp(&self, other: &ThinArc<H, T>) -> Option<Ordering> {
        ThinArc::with_arc(self, |a| ThinArc::with_arc(other, |b| a.partial_cmp(b)))
    }
}

impl<H: Ord, T: Ord> Ord for ThinArc<H, T> {
    #[inline]
    fn cmp(&self, other: &ThinArc<H, T>) -> Ordering {
        ThinArc::with_arc(self, |a| ThinArc::with_arc(other, |b| a.cmp(b)))
    }
}

impl<H: Hash, T: Hash> Hash for ThinArc<H, T> {
    fn hash<HSR: Hasher>(&self, state: &mut HSR) {
        ThinArc::with_arc(self, |a| a.hash(state))
    }
}

impl<H: fmt::Debug, T: fmt::Debug> fmt::Debug for ThinArc<H, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<H, T> fmt::Pointer for ThinArc<H, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Pointer::fmt(&self.ptr(), f)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Arc, HeaderWithLength, ThinArc};
    use alloc::vec;
    use core::clone::Clone;
    use core::ops::Drop;
    use core::sync::atomic;
    use core::sync::atomic::Ordering::{Acquire, SeqCst};

    #[derive(PartialEq)]
    struct Canary(*mut atomic::AtomicUsize);

    impl Drop for Canary {
        fn drop(&mut self) {
            unsafe {
                (*self.0).fetch_add(1, SeqCst);
            }
        }
    }

    #[test]
    fn empty_thin() {
        let header = HeaderWithLength::new(100u32, 0);
        let x = Arc::from_header_and_iter(header, core::iter::empty::<i32>());
        let y = Arc::into_thin(x.clone());
        assert_eq!(y.header.header, 100);
        assert!(y.slice.is_empty());
        assert_eq!(x.header.header, 100);
        assert!(x.slice.is_empty());
    }

    #[test]
    fn thin_assert_padding() {
        #[derive(Clone, Default)]
        #[repr(C)]
        struct Padded {
            i: u16,
        }

        // The header will have more alignment than `Padded`
        let header = HeaderWithLength::new(0i32, 2);
        let items = vec![Padded { i: 0xdead }, Padded { i: 0xbeef }];
        let a = ThinArc::from_header_and_iter(header, items.into_iter());
        assert_eq!(a.slice.len(), 2);
        assert_eq!(a.slice[0].i, 0xdead);
        assert_eq!(a.slice[1].i, 0xbeef);
    }

    #[test]
    #[allow(clippy::redundant_clone, clippy::eq_op)]
    fn slices_and_thin() {
        let mut canary = atomic::AtomicUsize::new(0);
        let c = Canary(&mut canary as *mut atomic::AtomicUsize);
        let v = vec![5, 6];
        let header = HeaderWithLength::new(c, v.len());
        {
            let x = Arc::into_thin(Arc::from_header_and_slice(header, &v));
            let y = ThinArc::with_arc(&x, |q| q.clone());
            let _ = y.clone();
            let _ = x == x;
            Arc::from_thin(x.clone());
        }
        assert_eq!(canary.load(Acquire), 1);
    }

    #[test]
    #[allow(clippy::redundant_clone, clippy::eq_op)]
    fn iter_and_thin() {
        let mut canary = atomic::AtomicUsize::new(0);
        let c = Canary(&mut canary as *mut atomic::AtomicUsize);
        let v = vec![5, 6];
        let header = HeaderWithLength::new(c, v.len());
        {
            let x = Arc::into_thin(Arc::from_header_and_iter(header, v.into_iter()));
            let y = ThinArc::with_arc(&x, |q| q.clone());
            let _ = y.clone();
            let _ = x == x;
            Arc::from_thin(x.clone());
        }
        assert_eq!(canary.load(Acquire), 1);
    }

    #[test]
    fn into_raw_and_from_raw() {
        let mut canary = atomic::AtomicUsize::new(0);
        let c = Canary(&mut canary as *mut atomic::AtomicUsize);
        let v = vec![5, 6];
        let header = HeaderWithLength::new(c, v.len());
        {
            type ThinArcCanary = ThinArc<Canary, u32>;
            let x: ThinArcCanary = Arc::into_thin(Arc::from_header_and_iter(header, v.into_iter()));
            let ptr = x.as_ptr();

            assert_eq!(x.into_raw(), ptr);

            let _x = unsafe { ThinArcCanary::from_raw(ptr) };
        }
        assert_eq!(canary.load(Acquire), 1);
    }

    #[test]
    fn thin_eq_and_cmp() {
        [
            [("*", &b"AB"[..]), ("*", &b"ab"[..])],
            [("*", &b"AB"[..]), ("*", &b"a"[..])],
            [("*", &b"A"[..]), ("*", &b"ab"[..])],
            [("A", &b"*"[..]), ("a", &b"*"[..])],
            [("a", &b"*"[..]), ("A", &b"*"[..])],
            [("AB", &b"*"[..]), ("a", &b"*"[..])],
            [("A", &b"*"[..]), ("ab", &b"*"[..])],
        ]
        .iter()
        .for_each(|[lt @ (lh, ls), rt @ (rh, rs)]| {
            let l = ThinArc::from_header_and_slice(lh, ls);
            let r = ThinArc::from_header_and_slice(rh, rs);

            assert_eq!(l, l);
            assert_eq!(r, r);

            assert_ne!(l, r);
            assert_ne!(r, l);

            assert_eq!(l <= l, lt <= lt, "{lt:?} <= {lt:?}");
            assert_eq!(l >= l, lt >= lt, "{lt:?} >= {lt:?}");

            assert_eq!(l < l, lt < lt, "{lt:?} < {lt:?}");
            assert_eq!(l > l, lt > lt, "{lt:?} > {lt:?}");

            assert_eq!(r <= r, rt <= rt, "{rt:?} <= {rt:?}");
            assert_eq!(r >= r, rt >= rt, "{rt:?} >= {rt:?}");

            assert_eq!(r < r, rt < rt, "{rt:?} < {rt:?}");
            assert_eq!(r > r, rt > rt, "{rt:?} > {rt:?}");

            assert_eq!(l < r, lt < rt, "{lt:?} < {rt:?}");
            assert_eq!(r > l, rt > lt, "{rt:?} > {lt:?}");
        })
    }

    #[test]
    fn thin_eq_and_partial_cmp() {
        [
            [(0.0, &[0.0, 0.0][..]), (1.0, &[0.0, 0.0][..])],
            [(1.0, &[0.0, 0.0][..]), (0.0, &[0.0, 0.0][..])],
            [(0.0, &[0.0][..]), (0.0, &[0.0, 0.0][..])],
            [(0.0, &[0.0, 0.0][..]), (0.0, &[0.0][..])],
            [(0.0, &[1.0, 2.0][..]), (0.0, &[10.0, 20.0][..])],
        ]
        .iter()
        .for_each(|[lt @ (lh, ls), rt @ (rh, rs)]| {
            let l = ThinArc::from_header_and_slice(lh, ls);
            let r = ThinArc::from_header_and_slice(rh, rs);

            assert_eq!(l, l);
            assert_eq!(r, r);

            assert_ne!(l, r);
            assert_ne!(r, l);

            assert_eq!(l <= l, lt <= lt, "{lt:?} <= {lt:?}");
            assert_eq!(l >= l, lt >= lt, "{lt:?} >= {lt:?}");

            assert_eq!(l < l, lt < lt, "{lt:?} < {lt:?}");
            assert_eq!(l > l, lt > lt, "{lt:?} > {lt:?}");

            assert_eq!(r <= r, rt <= rt, "{rt:?} <= {rt:?}");
            assert_eq!(r >= r, rt >= rt, "{rt:?} >= {rt:?}");

            assert_eq!(r < r, rt < rt, "{rt:?} < {rt:?}");
            assert_eq!(r > r, rt > rt, "{rt:?} > {rt:?}");

            assert_eq!(l < r, lt < rt, "{lt:?} < {rt:?}");
            assert_eq!(r > l, rt > lt, "{rt:?} > {lt:?}");
        })
    }

    #[allow(dead_code)]
    const fn is_partial_ord<T: ?Sized + PartialOrd>() {}

    #[allow(dead_code)]
    const fn is_ord<T: ?Sized + Ord>() {}

    // compile-time check that PartialOrd/Ord is correctly derived
    const _: () = is_partial_ord::<ThinArc<f64, f64>>();
    const _: () = is_partial_ord::<ThinArc<f64, u64>>();
    const _: () = is_partial_ord::<ThinArc<u64, f64>>();
    const _: () = is_ord::<ThinArc<u64, u64>>();
}
