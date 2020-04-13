// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Fork of Arc. This has the following advantages over std::sync::Arc:
//!
//! * `triomphe::Arc` doesn't support weak references: we save space by excluding the weak reference count, and we don't do extra read-modify-update operations to handle the possibility of weak references.
//! * `triomphe::UniqueArc` allows one to construct a temporarily-mutable `Arc` which can be converted to a regular `triomphe::Arc` later
//! * `triomphe::OffsetArc` can be used transparently from C++ code and is compatible with (and can be converted to/from) `triomphe::Arc`
//! * `triomphe::ArcBorrow` is functionally similar to `&triomphe::Arc<T>`, however in memory it's simply `&T`. This makes it more flexible for FFI; the source of the borrow need not be an `Arc` pinned on the stack (and can instead be a pointer from C++, or an `OffsetArc`). Additionally, this helps avoid pointer-chasing.
//! * `triomphe::Arc` has can be constructed for dynamically-sized types via `from_header_and_iter`
//! * `triomphe::ThinArc` provides thin-pointer `Arc`s to dynamically sized types
//! * `triomphe::ArcUnion` is union of two `triomphe:Arc`s which fits inside one word of memory
//!

#![allow(missing_docs)]

#[macro_use]
extern crate memoffset;
extern crate serde;
extern crate stable_deref_trait;

use serde::{Deserialize, Serialize};
use stable_deref_trait::{CloneStableDeref, StableDeref};
use std::alloc::Layout;
use std::borrow;
use std::cmp::Ordering;
use std::convert::From;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter::{ExactSizeIterator, Iterator};
use std::marker::PhantomData;
use std::mem;
use std::mem::ManuallyDrop;
use std::ops::{Deref, DerefMut};
use std::os::raw::c_void;
use std::process;
use std::ptr;
use std::slice;
use std::sync::atomic;
use std::sync::atomic::Ordering::{Acquire, Relaxed, Release};
use std::{isize, usize};

/// A soft limit on the amount of references that may be made to an `Arc`.
///
/// Going above this limit will abort your program (although not
/// necessarily) at _exactly_ `MAX_REFCOUNT + 1` references.
const MAX_REFCOUNT: usize = (isize::MAX) as usize;

/// An atomically reference counted shared pointer
///
/// See the documentation for [`Arc`] in the standard library. Unlike the
/// standard library `Arc`, this `Arc` does not support weak reference counting.
///
/// [`Arc`]: https://doc.rust-lang.org/stable/std/sync/struct.Arc.html
#[repr(C)]
pub struct Arc<T: ?Sized> {
    p: ptr::NonNull<ArcInner<T>>,
}

/// An `Arc` that is known to be uniquely owned
///
/// When `Arc`s are constructed, they are known to be
/// uniquely owned. In such a case it is safe to mutate
/// the contents of the `Arc`. Normally, one would just handle
/// this by mutating the data on the stack before allocating the
/// `Arc`, however it's possible the data is large or unsized
/// and you need to heap-allocate it earlier in such a way
/// that it can be freely converted into a regular `Arc` once you're
/// done.
///
/// `UniqueArc` exists for this purpose, when constructed it performs
/// the same allocations necessary for an `Arc`, however it allows mutable access.
/// Once the mutation is finished, you can call `.shareable()` and get a regular `Arc`
/// out of it.
///
/// ```rust
/// # use triomphe::UniqueArc;
/// let data = [1, 2, 3, 4, 5];
/// let mut x = UniqueArc::new(data);
/// x[4] = 7; // mutate!
/// let y = x.shareable(); // y is an Arc<T>
/// ```
pub struct UniqueArc<T: ?Sized>(Arc<T>);

impl<T> UniqueArc<T> {
    #[inline]
    /// Construct a new UniqueArc
    pub fn new(data: T) -> Self {
        UniqueArc(Arc::new(data))
    }

    #[inline]
    /// Convert to a shareable Arc<T> once we're done mutating it
    pub fn shareable(self) -> Arc<T> {
        self.0
    }
}

impl<T> Deref for UniqueArc<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &*self.0
    }
}

impl<T> DerefMut for UniqueArc<T> {
    fn deref_mut(&mut self) -> &mut T {
        // We know this to be uniquely owned
        unsafe { &mut (*self.0.ptr()).data }
    }
}

unsafe impl<T: ?Sized + Sync + Send> Send for Arc<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Arc<T> {}

/// The object allocated by an Arc<T>
#[repr(C)]
struct ArcInner<T: ?Sized> {
    count: atomic::AtomicUsize,
    data: T,
}

unsafe impl<T: ?Sized + Sync + Send> Send for ArcInner<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for ArcInner<T> {}

impl<T> Arc<T> {
    /// Construct an `Arc<T>`
    #[inline]
    pub fn new(data: T) -> Self {
        let x = Box::new(ArcInner {
            count: atomic::AtomicUsize::new(1),
            data: data,
        });
        unsafe {
            Arc {
                p: ptr::NonNull::new_unchecked(Box::into_raw(x)),
            }
        }
    }

    /// Convert the Arc<T> to a raw pointer, suitable for use across FFI
    ///
    /// Note: This returns a pointer to the data T, which is offset in the allocation.
    ///
    /// It is recommended to use OffsetArc for this.
    #[inline]
    fn into_raw(this: Self) -> *const T {
        let ptr = unsafe { &((*this.ptr()).data) as *const _ };
        mem::forget(this);
        ptr
    }

    /// Reconstruct the Arc<T> from a raw pointer obtained from into_raw()
    ///
    /// Note: This raw pointer will be offset in the allocation and must be preceded
    /// by the atomic count.
    ///
    /// It is recommended to use OffsetArc for this
    #[inline]
    unsafe fn from_raw(ptr: *const T) -> Self {
        // To find the corresponding pointer to the `ArcInner` we need
        // to subtract the offset of the `data` field from the pointer.
        let ptr = (ptr as *const u8).sub(offset_of!(ArcInner<T>, data));
        Arc {
            p: ptr::NonNull::new_unchecked(ptr as *mut ArcInner<T>),
        }
    }

    /// Produce a pointer to the data that can be converted back
    /// to an Arc. This is basically an `&Arc<T>`, without the extra indirection.
    /// It has the benefits of an `&T` but also knows about the underlying refcount
    /// and can be converted into more `Arc<T>`s if necessary.
    #[inline]
    pub fn borrow_arc<'a>(&'a self) -> ArcBorrow<'a, T> {
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
}

impl<T: ?Sized> Arc<T> {
    #[inline]
    fn inner(&self) -> &ArcInner<T> {
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

    fn ptr(&self) -> *mut ArcInner<T> {
        self.p.as_ptr()
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
            process::abort();
        }

        unsafe {
            Arc {
                p: ptr::NonNull::new_unchecked(self.ptr()),
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

impl<T: Clone> Arc<T> {
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

    /// Whether or not the `Arc` is uniquely owned (is the refcount 1?)
    #[inline]
    pub fn is_unique(&self) -> bool {
        // See the extensive discussion in [1] for why this needs to be Acquire.
        //
        // [1] https://github.com/servo/servo/issues/21186
        self.inner().count.load(Acquire) == 1
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

unsafe impl<T: ?Sized> StableDeref for Arc<T> {}
unsafe impl<T: ?Sized> CloneStableDeref for Arc<T> {}

impl<'de, T: Deserialize<'de>> Deserialize<'de> for Arc<T> {
    fn deserialize<D>(deserializer: D) -> Result<Arc<T>, D::Error>
    where
        D: ::serde::de::Deserializer<'de>,
    {
        T::deserialize(deserializer).map(Arc::new)
    }
}

impl<T: Serialize> Serialize for Arc<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ::serde::ser::Serializer,
    {
        (**self).serialize(serializer)
    }
}

#[cfg(feature = "arc-swap")]
unsafe impl<T: ?Sized + Clone> arc_swap::RefCnt for Arc<T> {
    type Base = T;

    #[inline]
    fn into_ptr(me: Self) -> *mut Self::Base {
        Arc::into_raw(me) as *mut T
    }

    #[inline]
    fn as_ptr(me: &Self) -> *mut Self::Base {
        me.as_ref() as *const T as *mut T
    }

    #[inline]
    unsafe fn from_ptr(ptr: *const Self::Base) -> Self {
        Arc::from_raw(ptr)
    }
}

/// Structure to allow Arc-managing some fixed-sized data and a variably-sized
/// slice in a single allocation.
#[derive(Debug, Eq, PartialEq, PartialOrd)]
pub struct HeaderSlice<H, T: ?Sized> {
    /// The fixed-sized data.
    pub header: H,

    /// The dynamically-sized data.
    pub slice: T,
}

impl<H, T> Arc<HeaderSlice<H, [T]>> {
    /// Creates an Arc for a HeaderSlice using the given header struct and
    /// iterator to generate the slice. The resulting Arc will be fat.
    #[inline]
    pub fn from_header_and_iter<I>(header: H, mut items: I) -> Self
    where
        I: Iterator<Item = T> + ExactSizeIterator,
    {
        assert_ne!(mem::size_of::<T>(), 0, "Need to think about ZST");

        let num_items = items.len();

        // Offset of the start of the slice in the allocation.
        let inner_to_data_offset = offset_of!(ArcInner<HeaderSlice<H, [T; 1]>>, data);
        let data_to_slice_offset = offset_of!(HeaderSlice<H, [T; 1]>, slice);
        let slice_offset = inner_to_data_offset + data_to_slice_offset;

        // Compute the size of the real payload.
        let slice_size = mem::size_of::<T>()
            .checked_mul(num_items)
            .expect("size overflows");
        let usable_size = slice_offset
            .checked_add(slice_size)
            .expect("size overflows");

        // Round up size to alignment.
        let align = mem::align_of::<ArcInner<HeaderSlice<H, [T; 1]>>>();
        let size = usable_size.wrapping_add(align - 1) & !(align - 1);
        assert!(size >= usable_size, "size overflows");
        let layout = Layout::from_size_align(size, align).expect("invalid layout");

        let ptr: *mut ArcInner<HeaderSlice<H, [T]>>;
        unsafe {
            let buffer = std::alloc::alloc(layout);
            if buffer.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            // Synthesize the fat pointer. We do this by claiming we have a direct
            // pointer to a [T], and then changing the type of the borrow. The key
            // point here is that the length portion of the fat pointer applies
            // only to the number of elements in the dynamically-sized portion of
            // the type, so the value will be the same whether it points to a [T]
            // or something else with a [T] as its last member.
            let fake_slice: &mut [T] = slice::from_raw_parts_mut(buffer as *mut T, num_items);
            ptr = fake_slice as *mut [T] as *mut ArcInner<HeaderSlice<H, [T]>>;

            // Write the data.
            //
            // Note that any panics here (i.e. from the iterator) are safe, since
            // we'll just leak the uninitialized memory.
            ptr::write(&mut ((*ptr).count), atomic::AtomicUsize::new(1));
            ptr::write(&mut ((*ptr).data.header), header);
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

        // Return the fat Arc.
        assert_eq!(
            mem::size_of::<Self>(),
            mem::size_of::<usize>() * 2,
            "The Arc will be fat"
        );
        unsafe {
            Arc {
                p: ptr::NonNull::new_unchecked(ptr),
            }
        }
    }
}

/// Header data with an inline length. Consumers that use HeaderWithLength as the
/// Header type in HeaderSlice can take advantage of ThinArc.
#[derive(Debug, Eq, PartialEq, PartialOrd)]
pub struct HeaderWithLength<H> {
    /// The fixed-sized data.
    pub header: H,

    /// The slice length.
    length: usize,
}

impl<H> HeaderWithLength<H> {
    /// Creates a new HeaderWithLength.
    pub fn new(header: H, length: usize) -> Self {
        HeaderWithLength {
            header: header,
            length: length,
        }
    }
}

type HeaderSliceWithLength<H, T> = HeaderSlice<HeaderWithLength<H>, T>;

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
/// `ThinArc` solves this by storing the length in the allocation itself,
/// via `HeaderSliceWithLength`.
#[repr(C)]
pub struct ThinArc<H, T> {
    ptr: *mut ArcInner<HeaderSliceWithLength<H, [T; 1]>>,
}

unsafe impl<H: Sync + Send, T: Sync + Send> Send for ThinArc<H, T> {}
unsafe impl<H: Sync + Send, T: Sync + Send> Sync for ThinArc<H, T> {}

// Synthesize a fat pointer from a thin pointer.
//
// See the comment around the analogous operation in from_header_and_iter.
fn thin_to_thick<H, T>(
    thin: *mut ArcInner<HeaderSliceWithLength<H, [T; 1]>>,
) -> *mut ArcInner<HeaderSliceWithLength<H, [T]>> {
    let len = unsafe { (*thin).data.header.length };
    let fake_slice: *mut [T] = unsafe { slice::from_raw_parts_mut(thin as *mut T, len) };

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
                p: ptr::NonNull::new_unchecked(thin_to_thick(self.ptr)),
            })
        };

        // Expose the transient Arc to the callback, which may clone it if it wants.
        let result = f(&transient);

        // Forward the result.
        result
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

    /// Returns the address on the heap of the ThinArc itself -- not the T
    /// within it -- for memory reporting.
    #[inline]
    pub fn heap_ptr(&self) -> *const c_void {
        self.ptr as *const ArcInner<T> as *const c_void
    }
}

impl<H, T> Deref for ThinArc<H, T> {
    type Target = HeaderSliceWithLength<H, [T]>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { &(*thin_to_thick(self.ptr)).data }
    }
}

impl<H, T> Clone for ThinArc<H, T> {
    #[inline]
    fn clone(&self) -> Self {
        ThinArc::with_arc(self, |a| Arc::into_thin(a.clone()))
    }
}

impl<H, T> Drop for ThinArc<H, T> {
    #[inline]
    fn drop(&mut self) {
        let _ = Arc::from_thin(ThinArc { ptr: self.ptr });
    }
}

impl<H, T> Arc<HeaderSliceWithLength<H, [T]>> {
    /// Converts an `Arc` into a `ThinArc`. This consumes the `Arc`, so the refcount
    /// is not modified.
    #[inline]
    pub fn into_thin(a: Self) -> ThinArc<H, T> {
        assert_eq!(
            a.header.length,
            a.slice.len(),
            "Length needs to be correct for ThinArc to work"
        );
        let fat_ptr: *mut ArcInner<HeaderSliceWithLength<H, [T]>> = a.ptr();
        mem::forget(a);
        let thin_ptr = fat_ptr as *mut [usize] as *mut usize;
        ThinArc {
            ptr: thin_ptr as *mut ArcInner<HeaderSliceWithLength<H, [T; 1]>>,
        }
    }

    /// Converts a `ThinArc` into an `Arc`. This consumes the `ThinArc`, so the refcount
    /// is not modified.
    #[inline]
    pub fn from_thin(a: ThinArc<H, T>) -> Self {
        let ptr = thin_to_thick(a.ptr);
        mem::forget(a);
        unsafe {
            Arc {
                p: ptr::NonNull::new_unchecked(ptr),
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

/// An `Arc`, except it holds a pointer to the T instead of to the
/// entire ArcInner. This struct is FFI-compatible.
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
/// but we can also convert it to a "regular" Arc<T> by removing the offset.
///
/// This is very useful if you have an Arc-containing struct shared between Rust and C++,
/// and wish for C++ to be able to read the data behind the `Arc` without incurring
/// an FFI call overhead.
#[derive(Eq)]
#[repr(C)]
pub struct OffsetArc<T> {
    ptr: ptr::NonNull<T>,
}

unsafe impl<T: Sync + Send> Send for OffsetArc<T> {}
unsafe impl<T: Sync + Send> Sync for OffsetArc<T> {}

impl<T> Deref for OffsetArc<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr.as_ptr() }
    }
}

impl<T> Clone for OffsetArc<T> {
    #[inline]
    fn clone(&self) -> Self {
        Arc::into_raw_offset(self.clone_arc())
    }
}

impl<T> Drop for OffsetArc<T> {
    fn drop(&mut self) {
        let _ = Arc::from_raw_offset(OffsetArc {
            ptr: self.ptr.clone(),
        });
    }
}

impl<T: fmt::Debug> fmt::Debug for OffsetArc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: PartialEq> PartialEq for OffsetArc<T> {
    fn eq(&self, other: &OffsetArc<T>) -> bool {
        *(*self) == *(*other)
    }

    fn ne(&self, other: &OffsetArc<T>) -> bool {
        *(*self) != *(*other)
    }
}

#[cfg(feature = "arc-swap")]
unsafe impl<T: ?Sized + Clone> arc_swap::RefCnt for OffsetArc<T> {
    type Base = T;

    #[inline]
    fn into_ptr(me: Self) -> *mut Self::Base {
        let ret = me.ptr.as_ptr();
        mem::forget(me);
        ret
    }

    #[inline]
    fn as_ptr(me: &Self) -> *mut Self::Base {
        me.ptr.as_ptr()
    }

    #[inline]
    unsafe fn from_ptr(ptr: *const Self::Base) -> Self {
        OffsetArc {
            ptr: ptr::NonNull::new_unchecked(ptr as *mut T),
        }
    }
}

impl<T> OffsetArc<T> {
    /// Temporarily converts |self| into a bonafide Arc and exposes it to the
    /// provided callback. The refcount is not modified.
    #[inline]
    pub fn with_arc<F, U>(&self, f: F) -> U
    where
        F: FnOnce(&Arc<T>) -> U,
    {
        // Synthesize transient Arc, which never touches the refcount of the ArcInner.
        let transient = unsafe { ManuallyDrop::new(Arc::from_raw(self.ptr.as_ptr())) };

        // Expose the transient Arc to the callback, which may clone it if it wants.
        let result = f(&transient);

        // Forward the result.
        result
    }

    /// If uniquely owned, provide a mutable reference
    /// Else create a copy, and mutate that
    ///
    /// This is functionally the same thing as `Arc::make_mut`
    #[inline]
    pub fn make_mut(&mut self) -> &mut T
    where
        T: Clone,
    {
        unsafe {
            // extract the OffsetArc as an owned variable
            let this = ptr::read(self);
            // treat it as a real Arc
            let mut arc = Arc::from_raw_offset(this);
            // obtain the mutable reference. Cast away the lifetime
            // This may mutate `arc`
            let ret = Arc::make_mut(&mut arc) as *mut _;
            // Store the possibly-mutated arc back inside, after converting
            // it to a OffsetArc again
            ptr::write(self, Arc::into_raw_offset(arc));
            &mut *ret
        }
    }

    /// Clone it as an `Arc`
    #[inline]
    pub fn clone_arc(&self) -> Arc<T> {
        OffsetArc::with_arc(self, |a| a.clone())
    }

    /// Produce a pointer to the data that can be converted back
    /// to an `Arc`
    #[inline]
    pub fn borrow_arc<'a>(&'a self) -> ArcBorrow<'a, T> {
        ArcBorrow(&**self)
    }
}

impl<T> Arc<T> {
    /// Converts an `Arc` into a `OffsetArc`. This consumes the `Arc`, so the refcount
    /// is not modified.
    #[inline]
    pub fn into_raw_offset(a: Self) -> OffsetArc<T> {
        unsafe {
            OffsetArc {
                ptr: ptr::NonNull::new_unchecked(Arc::into_raw(a) as *mut T),
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
}

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
pub struct ArcBorrow<'a, T: 'a>(&'a T);

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
    #[inline]
    pub unsafe fn from_ref(r: &'a T) -> Self {
        ArcBorrow(r)
    }

    /// Compare two `ArcBorrow`s via pointer equality. Will only return
    /// true if they come from the same allocation
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.0 as *const T == other.0 as *const T
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

        // Expose the transient Arc to the callback, which may clone it if it wants.
        let result = f(&transient);

        // Forward the result.
        result
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
    unsafe fn new(ptr: *mut ()) -> Self {
        ArcUnion {
            p: ptr::NonNull::new_unchecked(ptr),
            phantom_a: PhantomData,
            phantom_b: PhantomData,
        }
    }

    /// Returns true if the two values are pointer-equal.
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.p == other.p
    }

    /// Returns an enum representing a borrow of either A or B.
    pub fn borrow(&self) -> ArcUnionBorrow<A, B> {
        if self.is_first() {
            let ptr = self.p.as_ptr() as *const A;
            let borrow = unsafe { ArcBorrow::from_ref(&*ptr) };
            ArcUnionBorrow::First(borrow)
        } else {
            let ptr = ((self.p.as_ptr() as usize) & !0x1) as *const B;
            let borrow = unsafe { ArcBorrow::from_ref(&*ptr) };
            ArcUnionBorrow::Second(borrow)
        }
    }

    /// Creates an `ArcUnion` from an instance of the first type.
    pub fn from_first(other: Arc<A>) -> Self {
        unsafe { Self::new(Arc::into_raw(other) as *mut _) }
    }

    /// Creates an `ArcUnion` from an instance of the second type.
    pub fn from_second(other: Arc<B>) -> Self {
        unsafe { Self::new(((Arc::into_raw(other) as usize) | 0x1) as *mut _) }
    }

    /// Returns true if this `ArcUnion` contains the first type.
    pub fn is_first(&self) -> bool {
        self.p.as_ptr() as usize & 0x1 == 0
    }

    /// Returns true if this `ArcUnion` contains the second type.
    pub fn is_second(&self) -> bool {
        !self.is_first()
    }

    /// Returns a borrow of the first type if applicable, otherwise `None`.
    pub fn as_first(&self) -> Option<ArcBorrow<A>> {
        match self.borrow() {
            ArcUnionBorrow::First(x) => Some(x),
            ArcUnionBorrow::Second(_) => None,
        }
    }

    /// Returns a borrow of the second type if applicable, otherwise None.
    pub fn as_second(&self) -> Option<ArcBorrow<B>> {
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
                let _ = Arc::from_raw(&*x);
            },
            ArcUnionBorrow::Second(x) => unsafe {
                let _ = Arc::from_raw(&*x);
            },
        }
    }
}

impl<A: fmt::Debug, B: fmt::Debug> fmt::Debug for ArcUnion<A, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.borrow(), f)
    }
}

#[cfg(test)]
mod tests {
    use super::{Arc, HeaderWithLength, ThinArc};
    use std::clone::Clone;
    use std::ops::Drop;
    use std::sync::atomic;
    use std::sync::atomic::Ordering::{Acquire, SeqCst};

    #[derive(PartialEq, Clone)]
    struct Canary(*mut atomic::AtomicUsize);

    impl Drop for Canary {
        fn drop(&mut self) {
            unsafe {
                (*self.0).fetch_add(1, SeqCst);
            }
        }
    }

    #[test]
    fn slices_and_thin() {
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

    #[cfg(feature = "arc-swap")]
    #[test]
    // miri and arc-swap currently don't work together.
    // issue: https://github.com/vorner/arc-swap/issues/23
    #[cfg_attr(miri, ignore)]
    fn arc_swap_() {
        type ArcSwap<T> = arc_swap::ArcSwapAny<Arc<T>>;

        let mut canary = atomic::AtomicUsize::new(0);
        let c = Canary(&mut canary as *mut atomic::AtomicUsize);

        {
            let x = ArcSwap::from(Arc::new(c));
            let _ = x.clone();
        }
        assert_eq!(canary.load(Acquire), 1);
    }

    #[cfg(feature = "arc-swap")]
    #[test]
    #[cfg_attr(miri, ignore)]
    fn offset_arc_swap() {
        type ArcSwap<T> = arc_swap::ArcSwapAny<super::OffsetArc<T>>;

        let mut canary = atomic::AtomicUsize::new(0);
        let c = Canary(&mut canary as *mut atomic::AtomicUsize);

        {
            let x = ArcSwap::from(Arc::into_raw_offset(Arc::new(c)));
            let _ = x.clone();
        }
        assert_eq!(canary.load(Acquire), 1);
    }
}
