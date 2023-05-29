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
    ///     #[lsb_first]
    ///     pub struct BitfieldStruct24: 24 {
    ///         /// A 1-bit field with [`U1`] accessors.
    ///         pub bit: 1,
    ///         /// A 1-bit field with [`bool`] accessors.
    ///         pub flag: 1 as bool,
    ///         /// A 5-bit field with [`U5`] accessors.
    ///         pub multi_bit: 5,
    ///         /// A 3-bit field with [`CustomBitint3`] accessors.
    ///         pub custom_bitint: 3 as CustomBitint3,
    ///         /// An 8-bit field with [`CustomPrimitive8`] accessors.
    ///         pub custom_primitive: 8 as CustomPrimitive8,
    ///         ..
    ///     }
    /// }
    /// ```
    #[lsb_first]
    pub struct BitfieldStruct24: 24 {
        /// A 1-bit field with [`U1`] accessors.
        pub bit: 1,
        /// A 1-bit field with [`bool`] accessors.
        pub flag: 1 as bool,
        /// A 5-bit field with [`U5`] accessors.
        pub multi_bit: 5,
        /// A 3-bit field with [`CustomBitint3`] accessors.
        pub custom_bitint: 3 as CustomBitint3,
        /// An 8-bit field with [`CustomPrimitive8`] accessors.
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

    /// A bitfield enum one bit wide.
    ///
    /// This type is convertible to and from [`U1`].
    ///
    /// # Declaration
    ///
    /// ```
    /// # use mvbitfield::prelude::*;
    /// bitfield! {
    ///     pub enum BitfieldEnum1: 1 {
    ///         /// Logical false.
    ///         False,
    ///         /// Logical true.
    ///         True,
    ///     }
    /// }
    /// ```
    pub enum BitfieldEnum1: 1 {
        /// Logical false.
        False,
        /// Logical true.
        True,
    }

    /// A bitfield enum three bits wide.
    ///
    /// This type is convertible to and from [`U3`].
    ///
    /// # Declaration
    ///
    /// ```
    /// # use mvbitfield::prelude::*;
    /// bitfield! {
    ///     pub enum BitfieldEnum3: 3 {
    ///         /// The value `2`.
    ///         Two = 2,
    ///         /// The value `7`.
    ///         Seven = 7,
    ///         /// The value `5`.
    ///         Five = 5,
    ///         ..
    ///     }
    /// }
    /// ```
    pub enum BitfieldEnum3: 3 {
        /// The value `2`.
        Two = 2,
        /// The value `7`.
        Seven = 7,
        /// The value `5`.
        Five = 5,
        ..
    }

    /// A bitfield enum eight bits wide.
    ///
    /// This type is convertible to and from [`U8`] and `u8`.
    ///
    /// # Declaration
    ///
    /// ```
    /// # use mvbitfield::prelude::*;
    /// bitfield! {
    ///     pub enum BitfieldEnum8: 8 { .. }
    /// }
    /// ```
    pub enum BitfieldEnum8: 8 { .. }
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
