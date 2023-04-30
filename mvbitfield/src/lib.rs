#![cfg_attr(feature = "_nightly", feature(doc_cfg))]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
#![doc = include_str!("../../README.md")]
#![no_std]

use core::fmt::Debug;
use core::hash::Hash;

use bitint::prelude::*;

pub use bitint;

#[cfg(any(doc, feature = "doc"))]
#[cfg_attr(feature = "_nightly", doc(cfg(doc)))]
pub mod example;
#[cfg(any(doc, feature = "doc"))]
#[cfg_attr(feature = "_nightly", doc(cfg(doc)))]
pub mod overview;
pub mod prelude;

#[doc(hidden)]
pub mod __private {
    pub use mvbitfield_macros::bitfield;
}

mod sealed {
    pub trait Sealed {}
}

/// Bitfield struct types.
///
/// Bitfield structs have a `bitint` type and a primitive type. The `bitint`
/// type is the canonical integer representation of this type.
///
/// There are zero-cost conversions between the `Self` and the `bitint` type,
/// and from `Self` to the primitive type. There is a checked conversion from
/// the primitive type to `Self`, though some implementors may separately
/// provide a zero-cost conversion from the primitive type to `Self`.
pub trait BitfieldStruct:
    Copy + Debug + Eq + Hash + From<Self::Bitint> + TryFrom<<Self::Bitint as UBitint>::Primitive>
where
    <Self::Bitint as UBitint>::Primitive: From<Self>,
{
    /// The `bitint` type with zero-cost conversions to and from [`Self`].
    type Bitint: UBitint + From<Self>;

    /// The type's zero value.
    const ZERO: Self;

    /// Returns the type's zero value.
    fn zero() -> Self {
        Self::ZERO
    }

    /// Creates a bitfield value from a primitive value if it is in range for
    /// the `bitint` type.
    ///
    /// This is a convenience alias for [`UBitint::new`] and [`Into`].
    fn new(value: <Self::Bitint as UBitint>::Primitive) -> Option<Self> {
        <Self::Bitint as UBitint>::new(value).map(Into::into)
    }

    /// Creates a bitfield value by masking off the upper bits of a primitive
    /// value.
    ///
    /// This is a convenience alias for [`UBitint::new_masked`] and [`Into`].
    fn new_masked(value: <Self::Bitint as UBitint>::Primitive) -> Self {
        <Self::Bitint as UBitint>::new_masked(value).into()
    }

    /// Creates a bitfield value from a primitive value without checking whether
    /// it is in range for the `bitint` type.
    ///
    /// This zero-cost conversion is a convenience alias for
    /// [`UBitint::new_unchecked`] and [`Into`].
    ///
    /// # Safety
    ///
    /// The value must be in range for the `bitint` type, as determined by
    /// [`UBitint::is_in_range`].
    unsafe fn new_unchecked(value: <Self::Bitint as UBitint>::Primitive) -> Self {
        <Self::Bitint as UBitint>::new_unchecked(value).into()
    }
}

/// Generates bitfield structs.
///
/// See the [overview of concepts and terms](overview) and [examples](example).
///
#[doc = include_str!("../syntax.md")]
#[macro_export]
macro_rules! bitfield {
    ($($tt:tt)*) => {
        $crate::__private::bitfield! { ($crate, $($tt)*) }
    };
}

#[test]
fn trybuild_tests() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests_error/*.rs");
}
