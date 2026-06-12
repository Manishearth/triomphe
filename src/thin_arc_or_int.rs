use std::cmp::Ordering;
use std::ffi::c_void;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ptr::NonNull;

use crate::ThinArc;

/// A type representing either a signed pointer-sized integer (`isize`) or
/// a reference-counted pointer (`ThinArc<H, T>`).
///
/// Optimized using `NonNull` so that `Option<ThinArcOrInt<H, T>>` takes up exactly
/// the size of a single architecture pointer.
pub struct ThinArcOrInt<H, T> {
    raw: NonNull<c_void>,
    _marker: PhantomData<ThinArc<H, T>>,
}

pub const THIN_ARC_OR_INT_MAX: isize = isize::MAX >> 1;
pub const THIN_ARC_OR_INT_MIN: isize = isize::MIN >> 1;

unsafe impl<H, T> Send for ThinArcOrInt<H, T> where ThinArc<H, T>: Send {}
unsafe impl<H, T> Sync for ThinArcOrInt<H, T> where ThinArc<H, T>: Sync {}

impl<H, T> ThinArcOrInt<H, T> {
    const TAG_MASK: usize = 1;

    /// Constructs an instance from a signed integer.
    ///
    /// WARNING: The MSB of `val` is lost, as one bit in the internal representation is needed as a
    /// tag bit.
    pub fn from_isize(val: isize) -> Self {
        /// The value is bit-shifted left by 1 and the tag bit (LSB) is set to 1.
        let encoded = ((val as usize) << 1) | Self::TAG_MASK;

        // Safety: encoded is guaranteed to be non-zero because the LSB is set to 1.
        let raw = unsafe { NonNull::new_unchecked(encoded as *mut c_void) };

        Self {
            raw,
            _marker: PhantomData,
        }
    }

    /// Constructs an instance from a ThinArc pointer.
    /// (Assumes the pointer is aligned and its LSB is 0.)
    pub fn from_arc(arc: ThinArc<H, T>) -> Self {
        let ptr = ThinArc::into_raw(arc);
        let raw_usize = ptr as usize;

        debug_assert_eq!(raw_usize & Self::TAG_MASK, 0, "Pointer must be aligned!");

        // Safety: ThinArc allocations on the heap are never null.
        let raw = unsafe { NonNull::new_unchecked(ptr as *mut c_void) };

        Self {
            raw,
            _marker: PhantomData,
        }
    }

    pub fn has_number(&self) -> bool {
        (self.raw.as_ptr() as usize & Self::TAG_MASK) != 0
    }

    pub fn has_ref(&self) -> bool {
        !self.has_number()
    }

    /// Returns the integer value if present, or `None` otherwise.
    pub fn as_isize(&self) -> Option<isize> {
        if self.has_number() {
            Some((self.raw.as_ptr() as isize) >> 1)
        } else {
            None
        }
    }

    /// Returns a shared reference to the `ThinArc` if present, or `None` otherwise.
    pub fn as_arc(&self) -> Option<&ThinArc<H, T>> {
        if self.has_ref() {
            unsafe { Some(self.as_arc_internal()) }
        } else {
            None
        }
    }

    /// Returns a mutable reference to the `ThinArc` if present, or `None` otherwise.
    pub fn as_arc_mut(&mut self) -> Option<&mut ThinArc<H, T>> {
        if self.has_ref() {
            unsafe {
                let ptr = &mut self.raw as *mut NonNull<c_void> as *mut ThinArc<H, T>;
                Some(&mut *ptr)
            }
        } else {
            None
        }
    }

    unsafe fn as_arc_internal(&self) -> &ThinArc<H, T> {
        let ptr = &self.raw as *const NonNull<c_void> as *const ThinArc<H, T>;
        &*ptr
    }

    unsafe fn take_arc_internal(&mut self) -> ThinArc<H, T> {
        ThinArc::from_raw(self.raw.as_ptr() as *const c_void)
    }
}

impl<H, T> Default for ThinArcOrInt<H, T> {
    fn default() -> Self {
        Self::from_isize(0)
    }
}

impl<H, T> Drop for ThinArcOrInt<H, T> {
    fn drop(&mut self) {
        if self.has_ref() {
            let _arc = unsafe { self.take_arc_internal() };
        }
    }
}

impl<H, T> Clone for ThinArcOrInt<H, T> {
    fn clone(&self) -> Self {
        if self.has_number() {
            Self {
                raw: self.raw,
                _marker: PhantomData,
            }
        } else {
            let arc = unsafe { self.as_arc_internal() };
            let cloned_arc = arc.clone();
            Self::from_arc(cloned_arc)
        }
    }
}

impl<H, T> PartialEq for ThinArcOrInt<H, T>
where
    H: PartialEq,
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self.as_isize(), other.as_isize()) {
            (Some(s), Some(o)) => s == o,
            (None, None) => unsafe { self.as_arc_internal() == other.as_arc_internal() },
            _ => false,
        }
    }
}

impl<H, T> Eq for ThinArcOrInt<H, T>
where
    H: Eq,
    T: Eq,
{
}

impl<H, T> PartialOrd for ThinArcOrInt<H, T>
where
    H: PartialOrd,
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self.as_isize(), other.as_isize()) {
            (Some(s), Some(o)) => s.partial_cmp(&o),
            (None, None) => unsafe { self.as_arc_internal().partial_cmp(other.as_arc_internal()) },
            (Some(_), None) => Some(Ordering::Less),
            (None, Some(_)) => Some(Ordering::Greater),
        }
    }
}

impl<H, T> Ord for ThinArcOrInt<H, T>
where
    H: Ord,
    T: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
    }
}

impl<H, T> Hash for ThinArcOrInt<H, T>
where
    H: Hash,
    T: Hash,
{
    fn hash<S: Hasher>(&self, state: &mut S) {
        if let Some(num) = self.as_isize() {
            0.hash(state);
            num.hash(state);
        } else {
            1.hash(state);
            unsafe { self.as_arc_internal().hash(state) };
        }
    }
}

impl<H: fmt::Debug, T: fmt::Debug> fmt::Debug for ThinArcOrInt<H, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(num) = self.as_isize() {
            f.debug_tuple("ThinArcOrInt::Number").field(&num).finish()
        } else {
            f.debug_tuple("ThinArcOrInt::ThinArc")
                .field(self.as_arc().unwrap())
                .finish()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_size() {
        assert_eq!(
            std::mem::size_of::<ThinArcOrInt<(), String>>(),
            std::mem::size_of::<usize>()
        );
    }

    #[test]
    fn test_clone_and_drop() {
        let arc = ThinArc::from_header_and_slice((), "Shared data".as_bytes());
        let val1 = ThinArcOrInt::from_arc(arc);

        let val2 = val1.clone();

        assert_eq!(&val1.as_arc().unwrap().slice, "Shared data".as_bytes());
        assert!(std::ptr::eq(
            &val1.as_arc().unwrap().slice,
            &val2.as_arc().unwrap().slice
        ));
    }

    #[test]
    fn test_option_size_optimization() {
        assert_eq!(
            std::mem::size_of::<ThinArcOrInt<(), String>>(),
            std::mem::size_of::<usize>()
        );
        assert_eq!(
            std::mem::size_of::<Option<ThinArcOrInt<(), String>>>(),
            std::mem::size_of::<usize>()
        );
        assert_ne!(None, Some(ThinArcOrInt::<(), ()>::from_isize(0)));
    }

    #[test]
    fn test_negative_numbers() {
        let negative = ThinArcOrInt::<(), ()>::from_isize(-42);
        assert!(negative.has_number());
        assert_eq!(negative.as_isize(), Some(-42));
    }

    #[test]
    fn test_max_number() {
        let negative = ThinArcOrInt::<(), ()>::from_isize(THIN_ARC_OR_INT_MAX);
        assert!(negative.has_number());
        assert_eq!(negative.as_isize(), Some(THIN_ARC_OR_INT_MAX));
    }

    #[test]
    fn test_min_number() {
        let negative = ThinArcOrInt::<(), ()>::from_isize(THIN_ARC_OR_INT_MIN);
        assert!(negative.has_number());
        assert_eq!(negative.as_isize(), Some(THIN_ARC_OR_INT_MIN));
    }

    #[test]
    fn test_thin_arc() {
        // Fix: Use from_header_and_iter instead of ThinArc::new
        let arc = ThinArc::from_header_and_iter((), std::iter::once("Hello Rust".to_string()));
        let val = ThinArcOrInt::from_arc(arc);

        assert!(val.has_ref());
        assert!(!val.has_number());

        // Fix: Call .as_arc() instead of .as_ref()
        if let Some(arc_ref) = val.as_arc() {
            assert_eq!(arc_ref.slice[0], "Hello Rust");
        }
    }
}
