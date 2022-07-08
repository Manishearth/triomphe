use alloc::alloc::Layout;
use core::iter::{ExactSizeIterator, Iterator};
use core::marker::PhantomData;
use core::mem;
use core::ptr::{self, NonNull};
use core::usize;

use super::{Arc, ArcInner};

/// Structure to allow Arc-managing some fixed-sized data and a variably-sized
/// slice in a single allocation.
#[derive(Debug, Eq, PartialEq, Hash, PartialOrd)]
#[repr(C)]
pub struct HeaderSlice<H, T: ?Sized> {
    /// The fixed-sized data.
    pub header: H,

    /// The dynamically-sized data.
    pub slice: T,
}

impl<H, T> Arc<HeaderSlice<H, [T]>> {
    /// Creates an Arc for a HeaderSlice using the given header struct and
    /// iterator to generate the slice. The resulting Arc will be fat.
    pub fn from_header_and_iter<I>(header: H, mut items: I) -> Self
    where
        I: Iterator<Item = T> + ExactSizeIterator,
    {
        assert_ne!(mem::size_of::<T>(), 0, "Need to think about ZST");

        let num_items = items.len();

        // Offset of the start of the slice in the allocation.
        let inner_to_data_offset = offset_of!(ArcInner<HeaderSlice<H, [T; 0]>>, data);
        let data_to_slice_offset = offset_of!(HeaderSlice<H, [T; 0]>, slice);
        let slice_offset = inner_to_data_offset + data_to_slice_offset;

        let ptr: NonNull<ArcInner<HeaderSlice<H, [T]>>> = unsafe {
            let layout = Layout::new::<H>()
                .extend(Layout::array::<T>(num_items).unwrap())
                .unwrap()
                .0
                .pad_to_align();

            // Safety:
            // - the provided closure does not change the pointer (except for meta & type)
            // - the provided layout is valid for `HeaderSlice<H, [T]>`
            Arc::allocate_for_layout(layout, |mem| {
                // Synthesize the fat pointer. We do this by claiming we have a direct
                // pointer to a [T], and then changing the type of the borrow. The key
                // point here is that the length portion of the fat pointer applies
                // only to the number of elements in the dynamically-sized portion of
                // the type, so the value will be the same whether it points to a [T]
                // or something else with a [T] as its last member.
                let fake_slice = ptr::slice_from_raw_parts_mut(mem as *mut T, num_items);
                fake_slice as *mut ArcInner<HeaderSlice<H, [T]>>
            })
        };

        unsafe {
            // Write the data.
            //
            // Note that any panics here (i.e. from the iterator) are safe, since
            // we'll just leak the uninitialized memory.
            ptr::write(&mut ((*ptr.as_ptr()).data.header), header);
            if num_items != 0 {
                let mut current = (*ptr.as_ptr()).data.slice.as_mut_ptr();
                debug_assert_eq!(
                    current as usize - ptr.as_ptr() as *mut u8 as usize,
                    slice_offset
                );
                for _ in 0..num_items {
                    ptr::write(
                        current,
                        items
                            .next()
                            .expect("ExactSizeIterator over-reported length"),
                    );
                    current = current.offset(1);
                }
                assert!(
                    items.next().is_none(),
                    "ExactSizeIterator under-reported length"
                );
            }
            assert!(
                items.next().is_none(),
                "ExactSizeIterator under-reported length"
            );
        }

        // Safety: ptr is valid & the inner structure is fully initialized
        Arc {
            p: ptr,
            phantom: PhantomData,
        }
    }

    /// Creates an Arc for a HeaderSlice using the given header struct and
    /// iterator to generate the slice. The resulting Arc will be fat.
    pub fn from_header_and_slice(header: H, items: &[T]) -> Self
    where
        T: Copy,
    {
        assert_ne!(mem::size_of::<T>(), 0, "Need to think about ZST");

        let num_items = items.len();

        let ptr: NonNull<ArcInner<HeaderSlice<H, [T]>>> = unsafe {
            let layout = Layout::new::<H>()
                .extend(Layout::for_value::<[T]>(items))
                .unwrap()
                .0
                .pad_to_align();

            // Safety:
            // - the provided closure does not change the pointer (except for meta & type)
            // - the provided layout is valid for `HeaderSlice<H, [T]>`
            Arc::allocate_for_layout(layout, |mem| {
                // Synthesize the fat pointer. We do this by claiming we have a direct
                // pointer to a [T], and then changing the type of the borrow. The key
                // point here is that the length portion of the fat pointer applies
                // only to the number of elements in the dynamically-sized portion of
                // the type, so the value will be the same whether it points to a [T]
                // or something else with a [T] as its last member.
                let fake_slice = ptr::slice_from_raw_parts_mut(mem as *mut T, num_items);
                fake_slice as *mut ArcInner<HeaderSlice<H, [T]>>
            })
        };

        unsafe {
            // Write the data.
            ptr::write(&mut ((*ptr.as_ptr()).data.header), header);
            let dst = (*ptr.as_ptr()).data.slice.as_mut_ptr();
            ptr::copy_nonoverlapping(items.as_ptr(), dst, num_items);
        }

        // Safety: ptr is valid & the inner structure is fully initialized
        Arc {
            p: ptr,
            phantom: PhantomData,
        }
    }
}

impl<H> Arc<HeaderSlice<H, str>> {
    /// Creates an Arc for a HeaderSlice using the given header struct and
    /// a str slice to generate the slice. The resulting Arc will be fat.
    pub fn from_header_and_str(header: H, string: &str) -> Self {
        let bytes = Arc::from_header_and_slice(header, string.as_bytes());

        // Safety: `ArcInner` and `HeaderSlice` are `repr(C)`, `str` has the same layout as `[u8]`,
        //         thus it's ok to "transmute" between `Arc<HeaderSlice<H, [u8]>>` and `Arc<HeaderSlice<H, str>>`.
        //
        //         `bytes` are a valid string since we've just got them from a valid `str`.
        unsafe { Arc::from_raw_inner(Arc::into_raw_inner(bytes) as _) }
    }
}

/// Header data with an inline length. Consumers that use HeaderWithLength as the
/// Header type in HeaderSlice can take advantage of ThinArc.
#[derive(Debug, Eq, PartialEq, Hash, PartialOrd)]
#[repr(C)]
pub struct HeaderWithLength<H> {
    /// The fixed-sized data.
    pub header: H,

    /// The slice length.
    pub length: usize,
}

impl<H> HeaderWithLength<H> {
    /// Creates a new HeaderWithLength.
    #[inline]
    pub fn new(header: H, length: usize) -> Self {
        HeaderWithLength { header, length }
    }
}

impl<T: ?Sized> From<Arc<HeaderSlice<(), T>>> for Arc<T> {
    fn from(this: Arc<HeaderSlice<(), T>>) -> Self {
        debug_assert_eq!(
            Layout::for_value::<HeaderSlice<(), T>>(&this),
            Layout::for_value::<T>(&this.slice)
        );

        // Safety: `HeaderSlice<(), T>` and `T` has the same layout
        unsafe { Arc::from_raw_inner(Arc::into_raw_inner(this) as _) }
    }
}

impl<T: ?Sized> From<Arc<T>> for Arc<HeaderSlice<(), T>> {
    fn from(this: Arc<T>) -> Self {
        // Safety: `T` and `HeaderSlice<(), T>` has the same layout
        unsafe { Arc::from_raw_inner(Arc::into_raw_inner(this) as _) }
    }
}

impl<T: Copy> From<&[T]> for Arc<[T]> {
    fn from(slice: &[T]) -> Self {
        Arc::from_header_and_slice((), slice).into()
    }
}

impl From<&str> for Arc<str> {
    fn from(s: &str) -> Self {
        Arc::from_header_and_str((), s).into()
    }
}

impl From<String> for Arc<str> {
    fn from(s: String) -> Self {
        Self::from(&s[..])
    }
}

pub(crate) type HeaderSliceWithLength<H, T> = HeaderSlice<HeaderWithLength<H>, T>;

#[cfg(test)]
mod tests {
    use core::iter;

    use crate::{Arc, HeaderSlice};

    #[test]
    fn from_header_and_iter_smoke() {
        let arc = Arc::from_header_and_iter(
            (42u32, 17u8),
            IntoIterator::into_iter([1u16, 2, 3, 4, 5, 6, 7]),
        );

        assert_eq!(arc.header, (42, 17));
        assert_eq!(arc.slice, [1, 2, 3, 4, 5, 6, 7]);
    }

    #[test]
    fn from_header_and_slice_smoke() {
        let arc = Arc::from_header_and_slice((42u32, 17u8), &[1u16, 2, 3, 4, 5, 6, 7]);

        assert_eq!(arc.header, (42, 17));
        assert_eq!(arc.slice, [1u16, 2, 3, 4, 5, 6, 7]);
    }

    #[test]
    fn from_header_and_iter_empty() {
        let arc = Arc::from_header_and_iter((42u32, 17u8), iter::empty::<u16>());

        assert_eq!(arc.header, (42, 17));
        assert_eq!(arc.slice, []);
    }

    #[test]
    fn from_header_and_slice_empty() {
        let arc = Arc::from_header_and_slice((42u32, 17u8), &[1u16; 0]);

        assert_eq!(arc.header, (42, 17));
        assert_eq!(arc.slice, []);
    }

    #[test]
    fn issue_13_empty() {
        crate::Arc::from_header_and_iter((), iter::empty::<usize>());
    }

    #[test]
    fn issue_13_consumption() {
        let s: &[u8] = &[0u8; 255];
        crate::Arc::from_header_and_iter((), s.iter().copied());
    }

    #[test]
    fn from_header_and_str_smoke() {
        let a = Arc::from_header_and_str(
            42,
            "The answer to the ultimate question of life, the universe, and everything",
        );
        assert_eq!(a.header, 42);
        assert_eq!(
            &a.slice,
            "The answer to the ultimate question of life, the universe, and everything"
        );

        let empty = Arc::from_header_and_str((), "");
        assert_eq!(empty.header, ());
        assert_eq!(&empty.slice, "");
    }

    #[test]
    fn erase_and_create_from_thin_air_header() {
        let a: Arc<HeaderSlice<(), [u32]>> = Arc::from_header_and_slice((), &[12, 17, 16]);
        let b: Arc<[u32]> = a.into();

        assert_eq!(&*b, [12, 17, 16]);

        let c: Arc<HeaderSlice<(), [u32]>> = b.into();

        assert_eq!(&c.slice, [12, 17, 16]);
        assert_eq!(c.header, ());
    }
}
