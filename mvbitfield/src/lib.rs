//! `mvbitfield` generates types to work with bit-aligned fields.
//!
//! Bitfield structs serve roughly the same use cases as C/C++ structs with
//! bit-field members.
//!
//! The generated bitfield structs are:
//!
//! - **Endian-insensitive**, packing fields within an integer rather than
//!   across bytes or array elements.
//! - **Flexible and type-safe** with optional user-defined field accessor
//!   types.
//! - **Suitable for FFI and memory-mapped I/O** with care, as always.
//!
//! Bitfield enums are unit-only Rust enums with a declared bit width that can
//! be used as bitfield struct field accessors.
//!
//! # Demo
//!
//! ```
//! # #![allow(clippy::needless_doctest_main)]
//! // Recommended, but not required. The mvbitfield prelude includes the bitint
//! // prelude.
//! use mvbitfield::prelude::*;
//!
//! bitfield! {
//!     #[lsb_first]               // Field packing order.
//!     #[derive(PartialOrd, Ord)] // Other attributes are passed through.
//!     pub struct MyBitfieldStruct: 32 {
//!         // The lowest 3 bits with public bitint::U3 accessors.
//!         pub some_number: 3,
//!
//!         // The next 8 bits with public bitint::U8 accessors.
//!         pub another_number: 8,
//!
//!         // No accessors for field names starting with _.
//!         _padding: 2,
//!
//!         // Private bitint::U11 accessors.
//!         internal_number: 11,
//!
//!         // Skip unused bits, in this case 7 bits.
//!         ..,
//!
//!         // Private bool accessors.
//!         high_bit_flag: 1 as bool,
//!     }
//! }
//!
//! #[bitint_literals]
//! fn main() {
//!     // Use generated with_* methods to build bitfield structs.
//!     let x = MyBitfieldStruct::zero()
//!         .with_some_number(6_U3)
//!         .with_another_number(0xa5_U8)
//!         .with_internal_number(1025_U11)
//!         .with_high_bit_flag(true);
//!
//!     // Default accessors return bitints.
//!     assert_eq!(x.some_number(), 6_U3);
//!     assert_eq!(x.some_number().to_primitive(), 6);
//!     assert_eq!(x.another_number(), 0xa5_U8);
//!     assert_eq!(x.another_number().to_primitive(), 0xa5);
//!     assert_eq!(x.internal_number(), 1025_U11);
//!     assert_eq!(x.internal_number().to_primitive(), 1025);
//!
//!     // Custom accessors return the chosen type, which must have Into
//!     // conversions to and from the default accessor bitint.
//!     assert_eq!(x.high_bit_flag(), true);
//!
//!     // Zero-cost conversions to and from bitints and to primitive.
//!     assert_eq!(x.to_bitint(), 0b1_0000000_10000000001_00_10100101_110_U32);
//!     assert_eq!(x.to_primitive(), 0b1_0000000_10000000001_00_10100101_110);
//!     assert_eq!(x, MyBitfieldStruct::from_bitint(0x8080252e_U32));
//!
//!     // Zero-cost conversion from primitive, only for primitive-sized
//!     // bitfield structs.
//!     assert_eq!(x, MyBitfieldStruct::from_primitive(0x8080252e));
//! }
//! ```
//!
//! # Bitfield structs
//!
//! Bitfield structs are declared with a sequence of fields, but unlike regular
//! Rust structs those fields are not directly exposed. Instead, they are packed
//! into an integer and are only available by value through accessor methods
//! that perform the necessary shifting and masking operations.
//!
//! **Examples**
//!
//! See [`BitfieldStruct24`](example::BitfieldStruct24) and
//! [`BitfieldStruct32`](example::BitfieldStruct32) for [`bitfield!`]
//! invocations and the resulting generated types.
//!
//! ## Packing
//!
//! Fields occupy contiguous ranges of bits and are tightly packed in
//! declaration order. Each bit must be covered by precisely one field. The `..`
//! shorthand for a flexible field may be convenient to cover unused bits at
//! either end or in the middle.
//!
//! Packing begins with the first declared field at either the least or most
//! significant bit, depending on the [packing order
//! attribute](bitfield!#packing-order-attributes). If there is only one field,
//! it must cover every bit and the packing order attribute is optional.
//!
//! ## Associated types
//!
//! Bitfield structs have two associated types: a `bitint` type and a primitive
//! type. The `bitint` type is the bitfield struct's canonical integer
//! representation and is one of the 128 unsigned types from the [`mod@bitint`]
//! crate. The primitive type is the `bitint` type's primitive type.
//!
//! The [`BitfieldStruct::Bitint`], [`BitfieldStruct::Primitive`], and
//! [`UBitint::Primitive`] associated types model these relationships.
//!
//! ## Layout
//!
//! A bitfield struct has the same layout as its `bitint` type. Bitfield structs
//! of widths 8, 16, 32, 64, or 128 are particularly well suited for
//! memory-mapped I/O and foreign function interface bindings because their
//! `bitint` types have no forbidden bit patterns. Bitfield structs of other
//! widths require more care in unsafe contexts because their `bitint` types
//! have unused upper bits that must remain clear.
//!
//! ## Trait implementations
//!
//! Bitfield structs implement the [`BitfieldStruct`] trait and its
//! requirements:
//!
//! - [`Copy`] (and [`Clone`])
//! - [`Debug`]
//! - [`Eq`] (and [`PartialEq`])
//! - [`Hash`]
//! - [`From<Self::Bitint>`]
//! - [`TryFrom<Self::Primitive>`]
//! - [`Into<Self::Bitint>`]
//! - [`Into<Self::Primitive>`]
//!
//! You are free to provide more trait impls alongside the [`bitfield!`]
//! invocation, as with any other type. The [`bitfield!`] macro preserves
//! attributes it doesn't recognize and applies them to the generated type, so
//! you can request additional derives as well.
//!
//! ```
//! # use mvbitfield::prelude::*;
//! bitfield! {
//!     #[derive(PartialOrd, Ord)]
//!     #[msb_first]
//!     pub struct MyStruct: 12 {
//!         pub high_bit: 1 as bool,
//!         ..
//!     }
//! }
//!
//! trait MyOtherTrait {
//!     fn get_five() -> i32;
//! }
//!
//! impl MyOtherTrait for MyStruct {
//!     fn get_five() -> i32 { 5 }
//! }
//!
//! assert_eq!(MyStruct::get_five(), 5);
//! assert!(MyStruct::zero() < MyStruct::zero().with_high_bit(true));
//! ```
//!
//! ## Constructors and conversions
//!
//! Bitfield structs provide all of the [`BitfieldStruct`] trait methods and
//! conversions to and from the `bitint` and primitive type as `const` inherent
//! methods.
//!
//! ```ignore
//! impl MyBitfieldStruct {
//!     const fn zero() -> Self;
//!
//!     const fn new(value: Self::Primitive) -> Option<Self>;
//!
//!     const fn new_masked(value: Self::Primitive) -> Self;
//!
//!     const unsafe fn new_unchecked(value: Self::Primitive) -> Self;
//!
//!     const fn from_bitint(value: Self::Bitint) -> Self;
//!
//!     // Only for primitive widths.
//!     const fn from_primitive(value: Self::Primitive) -> Self;
//!
//!     const fn to_bitint(self) -> Self::Bitint;
//!
//!     const fn to_primitive(self) -> Self::Primitive;
//! }
//! ```
//!
//! ## Field accessors
//!
//! ```ignore
//! impl MyBitfieldStruct {
//!     fn my_field(self) -> T;
//!
//!     fn with_my_field(self, value: T) -> Self;
//!
//!     fn map_my_field(self, f: impl FnOnce(T) -> T) -> Self;
//!
//!     fn set_my_field(&mut self, value: T);
//!
//!     fn replace_my_field(&mut self, value: T) -> T;
//!
//!     fn update_my_field(&mut self, f: impl FnOnce(T) -> T) -> T;
//! }
//! ```
//!
//! where `my_field` is the field name and `T` is the field accessor type.
//!
//! # Bitfield enums
//!
//! ```
//! # use mvbitfield::prelude::*;
//! bitfield! {
//!     pub enum RenderMode: 3 {
//!         PointList,
//!         LineList,
//!         LineStrip,
//!         TriangleList,
//!         TriangleStrip,
//!         TriangleFan,
//!         QuadList,
//!         ..
//!     }
//! }
//!
//! #[bitint_literals]
//! fn main() {
//!     assert_eq!(RenderMode::from_bitint(4_U3), RenderMode::TriangleStrip);
//!     assert_eq!(RenderMode::TriangleStrip.to_bitint(), 4_U3);
//!     assert_eq!(RenderMode::TriangleStrip.to_primitive(), 4);
//!
//!     // Variants are generated for each unused discriminant.
//!     assert_eq!(RenderMode::from_bitint(7_U3), RenderMode::Unused7);
//! }
//! ```
//!
//! # Declaration syntax
//!
//! A detailed reference is provided with the [`bitfield!`] macro.
//!
#![cfg_attr(feature = "_nightly", feature(doc_cfg))]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
#![no_std]

use core::fmt::Debug;
use core::hash::Hash;

use bitint::prelude::*;

pub use ::bitint;

#[cfg(any(doc, feature = "doc"))]
#[cfg_attr(feature = "_nightly", doc(cfg(doc)))]
pub mod example;
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
/// Bitfield structs have a [`mod@bitint`] type and a primitive type. The
/// `bitint` type is the canonical integer representation. The primitive type is
/// the `bitint` type's primitive type.
///
/// There are zero-cost conversions between the `Self` and the `bitint` type,
/// and from `Self` to the primitive type. There is a checked conversion from
/// the primitive type to `Self`, though some implementors may separately
/// provide a zero-cost conversion from the primitive type to `Self`.
pub trait BitfieldStruct:
    Copy
    + Debug
    + Eq
    + Hash
    + From<Self::Bitint>
    + TryFrom<Self::Primitive>
    + Into<Self::Bitint>
    + Into<Self::Primitive>
{
    /// The bitfield struct's canonical integer representation.
    type Bitint: UBitint<Primitive = Self::Primitive> + From<Self> + Into<Self>;

    /// The `bitint` type's primitive type.
    type Primitive: From<Self> + TryInto<Self>;

    /// The type's zero value.
    const ZERO: Self;

    /// Returns the type's zero value.
    #[inline(always)]
    #[must_use]
    fn zero() -> Self {
        Self::ZERO
    }

    /// Creates a bitfield struct value from a primitive value if it is in range
    /// for the `bitint` type.
    #[must_use]
    fn new(value: Self::Primitive) -> Option<Self>;

    /// Creates a bitfield struct value by masking off the upper bits of a
    /// primitive value.
    #[must_use]
    fn new_masked(value: Self::Primitive) -> Self;

    /// Creates a bitfield struct value from a primitive value without checking
    /// whether it is in range for the `bitint` type.
    ///
    /// This is a zero-cost conversion.
    ///
    /// # Safety
    ///
    /// The value must be in range for the `bitint` type, as determined by
    /// [`UBitint::is_in_range`].
    #[must_use]
    unsafe fn new_unchecked(value: Self::Primitive) -> Self;
}

/// Generates bitfield struct types.
///
/// This page uses [notation from The Rust
/// Reference](https://doc.rust-lang.org/reference/notation.html) for syntax
/// grammar snippets. Tokens and production rules from Rust link to their
/// definitions in The Rust Reference. New production rules are unlinked and are
/// all defined on this page.
///
/// # Input
///
/// A `bitfield!` macro invocation must receive one _Input_ declaring zero or
/// more structs.
///
/// > **Syntax**
/// >
/// > _Input_ :
/// >
/// > > _Struct_<sup>\*</sup>
///
/// ## Bitfield struct declarations
///
/// **Syntax**
///
/// > _Struct_ :
/// >
/// > > [_OuterAttribute_][RefAttr]<sup>\*</sup>
/// >   [_Visibility_][RefVis]<sup>?</sup> `struct` [IDENTIFIER][RefIdent] `:`
/// >   [INTEGER_LITERAL][RefLitInt] `{` _Fields_<sup>?</sup> `}`
/// >
/// > _Fields_ :
/// >
/// > >  _Fields_ (`,` _Field_)<sup>\*</sup> `,`<sup>?</sup>
///
/// **Properties**
///
/// > Attributes
/// >
/// > * If the path is `lsb_first` or `msb_first`, interpreted as a [packing
/// >   order attribute](#packing-order-attributes).
/// > * Other attributes are applied to the generated type.
/// >
/// > Visibility
/// >
/// > * Applied to the generated type.
/// >
/// > Name
/// >
/// > * Names the generated type.
/// >
/// > Width
/// >
/// > * The bit width for packing. Determines the bitfield struct's `bitint` and
/// >   primitive types.
/// >
/// > Fields
/// >
/// > * One or more [bitfield struct fields](#bitfield-struct-fields).
///
/// **Example**
///
/// > ```
/// > # use mvbitfield::prelude::*;
/// > bitfield! {
/// >     pub struct MyStruct: 12 { .. }
/// > }
/// > ```
/// >
/// > This bitfield struct is twelve bits wide, so its bitint type is
/// > [`U12`](bitint::U12) and its primitive type is [`u16`].
///
/// ## Packing order attributes
///
/// Up to one packing order attribute may appear on a bitfield struct. A packing
/// order attribute is required on any bitfield struct with two or more fields.
///
/// **Syntax**
///
/// > `#[lsb_first]`
/// >
/// > * Sets the struct packing order to least-significant bit (LSB) first.
/// >
/// > `#[msb_first]`
/// >
/// > * Sets the struct packing order to most-significant bit (MSB) first.
///
/// **Example**
///
/// > ```
/// > # use mvbitfield::prelude::*;
/// > bitfield! {
/// >     #[lsb_first]
/// >     pub struct Foo: 8 {
/// >         pub low_bit: 1 as bool,
/// >         ..,
/// >         pub high_bit: 1 as bool,
/// >     }
/// >
/// >     #[msb_first]
/// >     pub struct Bar: 8 {
/// >         pub high_bit: 1 as bool,
/// >         ..,
/// >         pub low_bit: 1 as bool,
/// >     }
/// > }
/// >
/// > assert!(Foo::from_primitive(1).low_bit());
/// > assert!(Bar::from_primitive(1).low_bit());
/// > assert!(Foo::from_primitive(128).high_bit());
/// > assert!(Bar::from_primitive(128).high_bit());
/// > ```
///
/// ## Bitfield struct fields
///
/// Each field declared in a bitfield struct influences packing and may generate
/// accessor methods.
///
/// **Syntax**
///
/// > _Field_ :
/// >
/// > > [_OuterAttribute_][RefAttr]<sup>\*</sup>
/// > > [_Visibility_][RefVis]<sup>?</sup> ([IDENTIFIER][RefIdent] | `_`) `:`
/// >   ([INTEGER_LITERAL][RefLitInt] | `_`) (`as` [_Type_][RefType]
/// >   )<sup>?</sup>
/// >
/// > > | `..`
///
/// **Properties**
///
/// > Attributes
/// >
/// > * Currently reserved: Specifying a field attribute causes a compile error.
/// > * Omitted in the `..` form.
/// >
/// > Visibility
/// >
/// > * Applied to any accessor methods. May be any Rust visibility specifier.
/// > * Private in the `..` form.
/// >
/// > Name
/// >
/// > * If starting with `_`, this field has no accessor methods.
/// > * `_` in the `..` form.
/// > * Otherwise, this is the name prefix for accessor methods. May be any Rust
/// >   identifier, though some names may cause conflicts in the generated code,
/// >   causing a compile error.
/// >
/// > Width
/// >
/// > * Determines the `bitint` type. May be specified with an integer literal
/// >   or left flexible with `_`.
/// > * Flexible in the `..` form.
/// > * A bitfield struct may have up to one flexible field, which is sized to
/// >   occupy all of the one or more bits unused by other fields.
/// >
/// > Accessor type
/// >
/// > * Defaults to the field's `bitint` type if unspecified or in the `..`
/// >   form.
/// > * Appears in accessor method signatures.
/// > * Must have [`Into`] conversions to and from the field's `bitint` type,
/// >   assumed to be zero-cost.
/// >
/// >   Suitable types include:
/// >
/// >     * `bool` for 1-bit fields.
/// >     * Unsigned primitive integer types of the field's width.
/// >     * Unsigned `bitint` types of the field's width.
/// >     * Bitfield struct types of the field's width.
/// >     * And any user-defined types that meet that condition.
///
/// **Examples**
///
/// > ```
/// > # use mvbitfield::prelude::*;
/// > bitfield! {
/// >     #[lsb_first]
/// >     pub struct MyStruct: 10 {
/// >         pub my_bitint_field_a: 5,
/// >         pub my_bitint_field_b: 5 as U5
/// >     }
/// > }
/// > ```
/// >
/// > Public 5-bit fields with [`bitint::U5`] accessors.
/// >
/// > <br>
/// >
/// > ```
/// > # use mvbitfield::prelude::*;
/// > bitfield! {
/// >     pub struct MyStruct: 8 {
/// >         pub my_primitive_field: 8 as u8,
/// >     }
/// > }
/// > ```
/// >
/// > A public 8-bit field with [`u8`] accessors.
/// >
/// > <br>
/// >
/// > ```
/// > # use mvbitfield::prelude::*;
/// > bitfield! {
/// >     pub struct MyAccessor: 4 { .. }
/// >
/// >     pub struct MyStruct: 4 {
/// >         pub my_custom_field: 4 as MyAccessor,
/// >     }
/// > }
/// > ```
/// >
/// > `MyAccessor` is a bitfield struct with one private 4-bit field and no
/// > accessors. The field is declared with a flexible width and resolved to
/// > four bits at macro processing time to fill its bitfield struct. The field
/// > declarations `_: _` and `..` are equivalent.
/// >
/// > A public 4-bit field with `MyAccessor` accessors. The `MyAccessor` type is
/// > another bitfield struct in this example, but could be any other type
/// > having `impl From<U4> for MyAccessor` and `impl From<MyAccessor> for U4`.
/// >
/// > \
/// >
/// [RefAttr]: https://doc.rust-lang.org/reference/attributes.html
/// [RefIdent]: https://doc.rust-lang.org/reference/identifiers.html
/// [RefLitInt]:
///     https://doc.rust-lang.org/reference/tokens.html#integer-literals
/// [RefType]: https://doc.rust-lang.org/reference/types.html#type-expressions
/// [RefVis]: https://doc.rust-lang.org/reference/visibility-and-privacy.html
///
#[macro_export]
macro_rules! bitfield {
    ($($tt:tt)*) => {
        $crate::__private::bitfield! { ($crate, $($tt)*) }
    };
}

#[test]
#[cfg_attr(not(feature = "_trybuild_tests"), ignore)]
fn trybuild_tests() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests_error/*.rs");
}
