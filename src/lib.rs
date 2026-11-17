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
//! * `triomphe::ArcUnion` is union of two `triomphe::Arc`s which fits inside one word of memory
//!
//! With the optional `yoke` feature, `Arc`, `ThinArc`, `OffsetArc` and `ArcBorrow` implement [`yoke::CloneableCart`](https://docs.rs/yoke/latest/yoke/trait.CloneableCart.html) and can be used as cloneable [`Yoke`](https://docs.rs/yoke/latest/yoke/struct.Yoke.html) carts.

#![allow(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "unstable_dropck_eyepatch", feature(dropck_eyepatch))]

extern crate alloc;
#[cfg(feature = "std")]
extern crate core;

#[cfg(feature = "arc-swap")]
extern crate arc_swap;
#[cfg(feature = "serde")]
extern crate serde;
#[cfg(feature = "stable_deref_trait")]
extern crate stable_deref_trait;
#[cfg(feature = "unsize")]
extern crate unsize;
#[cfg(feature = "yoke")]
extern crate yoke;

mod alloc_error;
mod arc;
mod arc_borrow;
#[cfg(feature = "arc-swap")]
mod arc_swap_support;
mod arc_union;
mod header;
mod iterator_as_exact_size_iterator;
mod offset_arc;
mod thin_arc;
mod unique_arc;

pub use alloc_error::*;
pub use arc::*;
pub use arc_borrow::*;
pub use arc_union::*;
pub use header::*;
pub use offset_arc::*;
pub use thin_arc::*;
pub use unique_arc::*;

#[cfg(feature = "std")]
use std::process::abort;

// `no_std`-compatible abort by forcing a panic while already panicking.
#[cfg(not(feature = "std"))]
#[cold]
fn abort() -> ! {
    struct PanicOnDrop;
    impl Drop for PanicOnDrop {
        fn drop(&mut self) {
            panic!()
        }
    }
    let _double_panicer = PanicOnDrop;
    panic!();
}

/// Asserts that yokes cloned from (or projected off) one attached to `cart` keep borrowing
/// the cart's original `b"hello"` bytes, even after the original yoke is dropped.
#[cfg(all(test, feature = "yoke"))]
fn assert_yoke_clones_share_cart<C>(cart: C, project: fn(&C::Target) -> &[u8])
where
    C: yoke::CloneableCart + stable_deref_trait::StableDeref,
    C::Target: 'static,
{
    use yoke::Yoke;

    let yoke = Yoke::<&'static [u8], C>::attach_to_cart(cart, project);
    let data = yoke.get().as_ptr();
    let clone = yoke.clone();
    let tail: Yoke<&'static [u8], C> = yoke.map_project_cloned(|&bytes, _| &bytes[1..]);
    drop(yoke);

    assert_eq!(*clone.get(), b"hello");
    assert_eq!(clone.get().as_ptr(), data);
    assert_eq!(project(clone.backing_cart()).as_ptr(), data);
    assert_eq!(*tail.get(), b"ello");
    assert_eq!(tail.get().as_ptr(), data.wrapping_add(1));
}

// `ManuallyDrop::deref` is a `Deref` trait method, so it isn't callable in a
// `const fn` on our MSRV. This is a const-compatible substitute.
const fn mdref<T>(v: &core::mem::ManuallyDrop<T>) -> &T {
    // SAFETY: `ManuallyDrop<T>` is `repr(transparent)` over `T`, so `&ManuallyDrop<T>`
    // and `&T` have identical layout and this reference cast is sound.
    unsafe { core::mem::transmute(v) }
}
