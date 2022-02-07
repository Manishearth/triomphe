use alloc::alloc::Layout;
use core::iter::{ExactSizeIterator, Iterator};
use core::marker::PhantomData;
use core::mem;
use core::ptr;
use core::slice;
use core::sync::atomic;
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

        // Compute the size of the real payload.
        let slice_size = mem::size_of::<T>()
            .checked_mul(num_items)
            .expect("size overflows");
        let usable_size = slice_offset
            .checked_add(slice_size)
            .expect("size overflows");

        // Round up size to alignment.
        let align = mem::align_of::<ArcInner<HeaderSlice<H, [T; 0]>>>();
        let size = usable_size.wrapping_add(align - 1) & !(align - 1);
        assert!(size >= usable_size, "size overflows");
        let layout = Layout::from_size_align(size, align).expect("invalid layout");

        let ptr: *mut ArcInner<HeaderSlice<H, [T]>>;
        unsafe {
            let buffer = alloc::alloc::alloc(layout);
            if buffer.is_null() {
                alloc::alloc::handle_alloc_error(layout);
            }

            // Synthesize the fat pointer. We do this by claiming we have a direct
            // pointer to a [T], and then changing the type of the borrow. The key
            // point here is that the length portion of the fat pointer applies
            // only to the number of elements in the dynamically-sized portion of
            // the type, so the value will be the same whether it points to a [T]
            // or something else with a [T] as its last member.
            let fake_slice = ptr::slice_from_raw_parts_mut(buffer as *mut T, num_items);
            ptr = fake_slice as *mut ArcInner<HeaderSlice<H, [T]>>;

            let count = atomic::AtomicUsize::new(1);

            // Write the data.
            //
            // Note that any panics here (i.e. from the iterator) are safe, since
            // we'll just leak the uninitialized memory.
            ptr::write(&mut ((*ptr).count), count);
            ptr::write(&mut ((*ptr).data.header), header);
            if num_items != 0 {
                let mut current = (*ptr).data.slice.as_mut_ptr();
                debug_assert_eq!(current as usize - buffer as usize, slice_offset);
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

                // We should have consumed the buffer exactly.
                debug_assert_eq!(current as *mut u8, buffer.add(usable_size));
            }
            assert!(
                items.next().is_none(),
                "ExactSizeIterator under-reported length"
            );
        }

        // Return the fat Arc.
        assert_eq!(
            mem::size_of::<Self>(),
            mem::size_of::<usize>() * 2,
            "The Arc will be fat"
        );
        unsafe {
            Arc {
                p: ptr::NonNull::new_unchecked(ptr),
                phantom: PhantomData,
            }
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

        // Offset of the start of the slice in the allocation.
        let inner_to_data_offset = offset_of!(ArcInner<HeaderSlice<H, [T; 0]>>, data);
        let data_to_slice_offset = offset_of!(HeaderSlice<H, [T; 0]>, slice);
        let slice_offset = inner_to_data_offset + data_to_slice_offset;

        // Compute the size of the real payload.
        let slice_size = mem::size_of::<T>()
            .checked_mul(num_items)
            .expect("size overflows");
        let usable_size = slice_offset
            .checked_add(slice_size)
            .expect("size overflows");

        // Round up size to alignment.
        let align = mem::align_of::<ArcInner<HeaderSlice<H, [T; 0]>>>();
        let size = usable_size.wrapping_add(align - 1) & !(align - 1);
        assert!(size >= usable_size, "size overflows");
        let layout = Layout::from_size_align(size, align).expect("invalid layout");

        let ptr: *mut ArcInner<HeaderSlice<H, [T]>>;
        unsafe {
            let buffer = alloc::alloc::alloc(layout);
            if buffer.is_null() {
                alloc::alloc::handle_alloc_error(layout);
            }

            // Synthesize the fat pointer. We do this by claiming we have a direct
            // pointer to a [T], and then changing the type of the borrow. The key
            // point here is that the length portion of the fat pointer applies
            // only to the number of elements in the dynamically-sized portion of
            // the type, so the value will be the same whether it points to a [T]
            // or something else with a [T] as its last member.
            let fake_slice = ptr::slice_from_raw_parts_mut(buffer as *mut T, num_items);
            ptr = fake_slice as *mut ArcInner<HeaderSlice<H, [T]>>;

            let count = atomic::AtomicUsize::new(1);

            // Write the data.
            ptr::write(&mut ((*ptr).count), count);
            ptr::write(&mut ((*ptr).data.header), header);
            let current = (*ptr).data.slice.as_mut_ptr();
            ptr::copy_nonoverlapping(items.as_ptr(), current, num_items);
        }

        // Return the fat Arc.
        assert_eq!(
            mem::size_of::<Self>(),
            mem::size_of::<usize>() * 2,
            "The Arc will be fat"
        );
        unsafe {
            Arc {
                p: ptr::NonNull::new_unchecked(ptr),
                phantom: PhantomData,
            }
        }
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

pub(crate) type HeaderSliceWithLength<H, T> = HeaderSlice<HeaderWithLength<H>, T>;
