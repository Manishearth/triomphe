use core::fmt;
use core::marker::PhantomData;
use core::panic::{RefUnwindSafe, UnwindSafe};
use core::ptr;

use super::{Arc, ArcBorrow};

/// A tagged union that can represent `Arc<A>` or `Arc<B>` while only consuming a
/// single word. The type is also `NonNull`, and thus can be stored in an Option
/// without increasing size.
///
/// This is functionally equivalent to
/// `enum ArcUnion<A, B> { First(Arc<A>), Second(Arc<B>)` but only takes up
/// up a single word of stack space.
///
/// This could probably be extended to support four types if necessary.
pub struct ArcUnion<A, B> {
    // Safety invariant: `p` is a non-null pointer derived from `Arc::into_raw`
    // that owns one strong reference to a live `ArcInner<A>` (when `p.addr() & 1 == 0`)
    // or `ArcInner<B>` (when `p.addr() & 1 == 1`, with bit 0 set via `map_addr`).
    // Because `ArcInner<T>` is `#[repr(C)]` starting with `AtomicUsize` (whose
    // size and alignment are `align_of::<usize>() >= 2`), the `data` field
    // pointer returned by `Arc::into_raw` is always at least 2-byte aligned
    // (bit 0 is 0), and `p` retains full provenance over the `ArcInner` allocation.
    p: ptr::NonNull<()>,
    phantom_a: PhantomData<A>,
    phantom_b: PhantomData<B>,
}

// SAFETY:
// `ArcUnion<A, B>` logically owns either an `Arc<A>` or an `Arc<B>`. Moving it
// across threads requires both `Arc<A>: Send` (`A: Sync + Send`) and
// `Arc<B>: Send` (`B: Sync + Send`).
unsafe impl<A: Sync + Send, B: Send + Sync> Send for ArcUnion<A, B> {}

// SAFETY:
// Sharing `&ArcUnion<A, B>` across threads permits borrowing `&A` or `&B` and
// cloning the underlying `Arc`, which is sound when `A: Sync + Send` and
// `B: Sync + Send`.
unsafe impl<A: Sync + Send, B: Send + Sync> Sync for ArcUnion<A, B> {}

impl<A: RefUnwindSafe, B: RefUnwindSafe> UnwindSafe for ArcUnion<A, B> {}

impl<A: PartialEq, B: PartialEq> PartialEq for ArcUnion<A, B> {
    fn eq(&self, other: &Self) -> bool {
        use crate::ArcUnionBorrow::*;
        match (self.borrow(), other.borrow()) {
            (First(x), First(y)) => x == y,
            (Second(x), Second(y)) => x == y,
            (_, _) => false,
        }
    }
}

/// This represents a borrow of an `ArcUnion`.
#[derive(Debug)]
pub enum ArcUnionBorrow<'a, A: 'a, B: 'a> {
    First(ArcBorrow<'a, A>),
    Second(ArcBorrow<'a, B>),
}

impl<A, B> ArcUnion<A, B> {
    /// # Safety
    ///
    /// The caller must ensure that `ptr` is non-null, retains full provenance
    /// over a live `ArcInner<A>` or `ArcInner<B>` allocation from `Arc::into_raw`,
    /// transfers ownership of one strong reference to the returned `ArcUnion`,
    /// and has bit `0x1` clear if it points to `A` or set (via `map_addr`) if
    /// it points to `B`.
    const unsafe fn new(ptr: *mut ()) -> Self {
        ArcUnion {
            // SAFETY: By this function's `# Safety` precondition, `ptr` is non-null.
            p: unsafe { ptr::NonNull::new_unchecked(ptr) },
            phantom_a: PhantomData,
            phantom_b: PhantomData,
        }
    }

    /// Returns true if the two values are pointer-equal.
    #[inline]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.p == other.p
    }

    /// Reference count.
    #[inline]
    pub fn strong_count(this: &Self) -> usize {
        ArcUnionBorrow::strong_count(&this.borrow())
    }

    /// Returns an enum representing a borrow of either A or B.
    pub fn borrow(&self) -> ArcUnionBorrow<'_, A, B> {
        if self.is_first() {
            let ptr = self.p.as_ptr() as *const A;
            // SAFETY:
            // `self.is_first()` checked that bit `0x1` of `self.p` is 0. By
            // `ArcUnion::p`'s field invariant, `ptr` is the untagged pointer to
            // `A` obtained from `Arc::into_raw` with full provenance over the
            // live `ArcInner<A>` owned by `self` for the lifetime of `&self`.
            let borrow = unsafe { ArcBorrow::from_ptr(ptr) };
            ArcUnionBorrow::First(borrow)
        } else {
            let ptr = self.p.as_ptr().map_addr(|addr| addr & !0x1) as *const B;
            // SAFETY:
            // `!self.is_first()` means bit `0x1` of `self.p` is 1. By
            // `ArcUnion::p`'s field invariant, clearing bit `0x1` via `map_addr`
            // recovers the original 2-byte-aligned pointer to `B` from
            // `Arc::into_raw` while preserving full provenance over the live
            // `ArcInner<B>` owned by `self` for the lifetime of `&self`.
            let borrow = unsafe { ArcBorrow::from_ptr(ptr) };
            ArcUnionBorrow::Second(borrow)
        }
    }

    /// Creates an `ArcUnion` from an instance of the first type.
    #[inline]
    pub const fn from_first(other: Arc<A>) -> Self {
        // SAFETY:
        // `Arc::into_raw(other)` returns a non-null pointer to `ArcInner<A>::data`
        // with full provenance over `ArcInner<A>`, transferring ownership of one
        // strong reference. Because `ArcInner<A>` is `#[repr(C)]` with a leading
        // `AtomicUsize` (alignment >= 2), the offset and address of `data` are
        // even, so bit `0x1` is 0 as required for the `First` variant.
        unsafe { Self::new(Arc::into_raw(other) as *mut _) }
    }

    /// Creates an `ArcUnion` from an instance of the second type.
    #[inline]
    pub fn from_second(other: Arc<B>) -> Self {
        let ptr = Arc::into_raw(other);
        let tagged = ptr.map_addr(|addr| addr | 0x1);
        // SAFETY:
        // `ptr` came from `Arc::into_raw(other)` and is non-null with full
        // provenance over `ArcInner<B>` and an even address (bit `0x1` clear).
        // Setting bit `0x1` via `map_addr` preserves provenance and produces a
        // non-null pointer with bit `0x1` set, transferring ownership of one
        // strong reference for the `Second` variant.
        unsafe { Self::new(tagged as *mut _) }
    }

    /// Returns true if this `ArcUnion` contains the first type.
    #[inline]
    pub fn is_first(&self) -> bool {
        self.p.as_ptr() as usize & 0x1 == 0
    }

    /// Returns true if this `ArcUnion` contains the second type.
    #[inline]
    pub fn is_second(&self) -> bool {
        !self.is_first()
    }

    /// Returns a borrow of the first type if applicable, otherwise `None`.
    pub fn as_first(&self) -> Option<ArcBorrow<'_, A>> {
        match self.borrow() {
            ArcUnionBorrow::First(x) => Some(x),
            ArcUnionBorrow::Second(_) => None,
        }
    }

    /// Returns a borrow of the second type if applicable, otherwise None.
    pub fn as_second(&self) -> Option<ArcBorrow<'_, B>> {
        match self.borrow() {
            ArcUnionBorrow::First(_) => None,
            ArcUnionBorrow::Second(x) => Some(x),
        }
    }
}

impl<A, B> Clone for ArcUnion<A, B> {
    fn clone(&self) -> Self {
        match self.borrow() {
            ArcUnionBorrow::First(x) => ArcUnion::from_first(x.clone_arc()),
            ArcUnionBorrow::Second(x) => ArcUnion::from_second(x.clone_arc()),
        }
    }
}

impl<A, B> Drop for ArcUnion<A, B> {
    fn drop(&mut self) {
        match self.borrow() {
            // SAFETY:
            // `x` was constructed in `self.borrow()` from the untagged raw
            // pointer originally produced by `Arc::into_raw`. `ArcBorrow::to_raw(&x)`
            // extracts that pointer without creating an intermediate `&A`
            // reference, preserving provenance over the `ArcInner<A>` header.
            // Reconstructing and dropping `Arc<A>` consumes the single strong
            // reference owned by `*self`, which is being dropped and will not
            // be accessed again.
            ArcUnionBorrow::First(x) => unsafe {
                let _ = Arc::<A>::from_raw(ArcBorrow::to_raw(&x));
            },
            // SAFETY:
            // Same as the `First` arm for `ArcInner<B>`: `ArcBorrow::to_raw(&x)`
            // returns the untagged pointer with full `ArcInner<B>` provenance,
            // and dropping the reconstructed `Arc<B>` consumes the strong
            // reference owned by `*self`.
            ArcUnionBorrow::Second(x) => unsafe {
                let _ = Arc::<B>::from_raw(ArcBorrow::to_raw(&x));
            },
        }
    }
}

impl<A: fmt::Debug, B: fmt::Debug> fmt::Debug for ArcUnion<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.borrow(), f)
    }
}

impl<'a, A, B> ArcUnionBorrow<'a, A, B> {
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
        match this {
            ArcUnionBorrow::First(arc) => ArcBorrow::strong_count(arc),
            ArcUnionBorrow::Second(arc) => ArcBorrow::strong_count(arc),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn safe_arc_union_drop_reaches_refcount_through_data_pointer() {
        let union = ArcUnion::<u8, u64>::from_first(Arc::new(0xA5));
        drop(union);
    }

    #[test]
    fn arc_union_first_and_second_smoke() {
        let a = Arc::new(123_u32);
        let b = Arc::new(456_u64);

        let u_a = ArcUnion::<u32, u64>::from_first(a.clone());
        let u_b = ArcUnion::<u32, u64>::from_second(b.clone());

        assert!(u_a.is_first());
        assert!(!u_a.is_second());
        assert!(!u_b.is_first());
        assert!(u_b.is_second());

        assert_eq!(ArcUnion::strong_count(&u_a), 2);
        assert_eq!(ArcUnion::strong_count(&u_b), 2);

        assert_eq!(*u_a.as_first().unwrap(), 123);
        assert!(u_a.as_second().is_none());
        assert!(u_b.as_first().is_none());
        assert_eq!(*u_b.as_second().unwrap(), 456);

        let u_a2 = u_a.clone();
        assert_eq!(ArcUnion::strong_count(&u_a), 3);
        assert_eq!(u_a, u_a2);
        assert_ne!(u_a, u_b);

        drop(u_a2);
        assert_eq!(ArcUnion::strong_count(&u_a), 2);
        drop(u_a);
        assert_eq!(Arc::strong_count(&a), 1);

        drop(u_b);
        assert_eq!(Arc::strong_count(&b), 1);
    }

    #[test]
    fn arc_union_zst() {
        let a = Arc::new(());
        let b = Arc::new(());

        let u_a = ArcUnion::<(), ()>::from_first(a.clone());
        let u_b = ArcUnion::<(), ()>::from_second(b.clone());

        assert!(u_a.is_first());
        assert!(u_b.is_second());

        assert_eq!(ArcUnion::strong_count(&u_a), 2);
        assert_eq!(ArcUnion::strong_count(&u_b), 2);

        drop(u_a);
        drop(u_b);

        assert_eq!(Arc::strong_count(&a), 1);
        assert_eq!(Arc::strong_count(&b), 1);
    }
}
