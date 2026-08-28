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
    p: ptr::NonNull<()>,
    phantom_a: PhantomData<A>,
    phantom_b: PhantomData<B>,
}

unsafe impl<A: Sync + Send, B: Send + Sync> Send for ArcUnion<A, B> {}
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
    const unsafe fn new(ptr: *mut ()) -> Self {
        ArcUnion {
            p: ptr::NonNull::new_unchecked(ptr),
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
            let borrow = unsafe { ArcBorrow::from_ptr(ptr) };
            ArcUnionBorrow::First(borrow)
        } else {
            let ptr = self.p.as_ptr().map_addr(|addr| addr & !0x1) as *const B;
            let borrow = unsafe { ArcBorrow::from_ptr(ptr) };
            ArcUnionBorrow::Second(borrow)
        }
    }

    /// Creates an `ArcUnion` from an instance of the first type.
    #[inline]
    pub const fn from_first(other: Arc<A>) -> Self {
        unsafe { Self::new(Arc::into_raw(other) as *mut _) }
    }

    /// Creates an `ArcUnion` from an instance of the second type.
    #[inline]
    pub fn from_second(other: Arc<B>) -> Self {
        let ptr = Arc::into_raw(other);
        let tagged = ptr.map_addr(|addr| addr | 0x1);
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
            ArcUnionBorrow::First(x) => unsafe {
                let _ = Arc::from_raw(ArcBorrow::to_raw(&x));
            },
            ArcUnionBorrow::Second(x) => unsafe {
                let _ = Arc::from_raw(ArcBorrow::to_raw(&x));
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
