//! Example [`bitfield!`] invocations and their generated types.

use crate::prelude::*;

bitfield! {
    /// A bitfield struct 24 bits wide.
    ///
    /// This type is narrower than its primitive type---there is no
    /// `from_primitive` method, and [`TryFrom<u32>`] is provided for fallible
    /// conversion.
    ///
    /// # Declaration
    ///
    /// ```
    /// # use mvbitfield::prelude::*;
    /// # // This doctest can't see the custom types in the module, so declare
    /// # // some substitute types instead.
    /// # bitfield! {
    /// #     struct CustomBitint3: 3 { .. }
    /// #     struct CustomPrimitive8: 8 { .. }
    /// # }
    /// bitfield! {
    ///     /// A bitfield struct wrapping a `U24` `bitint`.
    ///     #[lsb_first]
    ///     pub struct BitfieldStruct24: 24 {
    ///         pub bit: 1,
    ///         pub flag: 1 as bool,
    ///         pub multi_bit: 5,
    ///         pub custom_bitint: 3 as CustomBitint3,
    ///         pub custom_primitive: 8 as CustomPrimitive8,
    ///         ..
    ///     }
    /// }
    /// ```
    #[lsb_first]
    pub struct BitfieldStruct24: 24 {
        pub bit: 1,
        pub flag: 1 as bool,
        pub multi_bit: 5,
        pub custom_bitint: 3 as CustomBitint3,
        pub custom_primitive: 8 as CustomPrimitive8,
        ..
    }

    /// A bitfield struct 32 bits wide.
    ///
    /// This type is the same width as its primitive---it provides an additional
    /// [`from_primitive`](Self::from_primitive) method and [`From<u32>`] impl
    /// for infallible, zero-cost conversion.
    ///
    /// # Declaration
    ///
    /// ```
    /// # use mvbitfield::prelude::*;
    /// # // This doctest can't see the custom types in the module, so declare
    /// # // some substitute types instead.
    /// # bitfield! {
    /// #     struct CustomBitint3: 3 { .. }
    /// #     struct CustomPrimitive8: 8 { .. }
    /// # }
    /// bitfield! {
    ///     /// A bitfield struct wrapping a `u32`.
    ///     #[lsb_first]
    ///     pub struct BitfieldStruct32: 32 {
    ///         pub bit: 1,
    ///         pub flag: 1 as bool,
    ///         pub multi_bit: 5,
    ///         pub custom_bitint: 3 as CustomBitint3,
    ///         pub custom_primitive: 8 as CustomPrimitive8,
    ///         ..
    ///     }
    /// }
    /// ```
    #[lsb_first]
    pub struct BitfieldStruct32: 32 {
        pub bit: 1,
        pub flag: 1 as bool,
        pub multi_bit: 5,
        pub custom_bitint: 3 as CustomBitint3,
        pub custom_primitive: 8 as CustomPrimitive8,
        ..
    }
}

/// A custom bitfield accessor that wraps a [`U3`] `bitint`.
pub struct CustomBitint3(pub U3);

impl From<U3> for CustomBitint3 {
    fn from(value: U3) -> Self {
        // Just wrap the provided bitint.
        Self(value)
    }
}

impl From<CustomBitint3> for U3 {
    fn from(value: CustomBitint3) -> Self {
        // Just return the wrapped bitint.
        value.0
    }
}

/// A custom bitfield accessor that wraps a [`u8`] primitive integer.
pub struct CustomPrimitive8(pub u8);

impl From<U8> for CustomPrimitive8 {
    fn from(value: U8) -> Self {
        // Convert through the primitive type; this has zero cost.
        Self(value.to_primitive())
    }
}

impl From<CustomPrimitive8> for U8 {
    fn from(value: CustomPrimitive8) -> Self {
        // Convert through the primitive type; this has zero cost.
        U8::from_primitive(value.0)
    }
}
