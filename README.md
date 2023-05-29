# mvbitfield

[![crates.io][crates-badge]][crates-url]
[![docs.rs][docs-badge]][docs-url]
[![CI Status][ci-badge]][ci-url]

[crates-badge]: https://img.shields.io/crates/v/mvbitfield
[crates-url]: https://crates.io/crates/mvbitfield
[docs-badge]: https://img.shields.io/docsrs/mvbitfield
[docs-url]: https://docs.rs/mvbitfield
[ci-badge]: https://img.shields.io/github/actions/workflow/status/mvanbem/mvbitfield/ci.yml?branch=main&label=CI&logo=github
[ci-url]: https://github.com/mvanbem/mvbitfield/actions?query=workflow%3ACI+branch%3Amain

A bitfield library for Rust.

`mvbitfield` generates types to work with bit-aligned fields.

Bitfield structs serve roughly the same use cases as C/C++ structs with
bit-field members and are:

- **Endian-insensitive**, packing fields within an integer rather than across
  bytes or array elements.
- **Flexible and type-safe** with optional user-defined field accessor types.
- **Suitable for FFI and memory-mapped I/O** with care, as always.

Bitfield enums are unit-only Rust enums with a declared bit width that provide
safe zero-cost conversions to and from an integer type and can be used as
accessors in a bitfield struct.

# Demo

```rust
// Recommended, but not required. The mvbitfield prelude includes
// the bitint prelude.
use mvbitfield::prelude::*;

bitfield! {
    #[lsb_first]               // Field packing order.
    #[derive(PartialOrd, Ord)] // Other attributes pass through.
    pub struct MyBitfieldStruct: 32 {
        // The lowest three bits with public bitint::U3 accessors.
        pub some_number: 3,

        // The next eight bits with public bitint::U8 accessors.
        pub another_number: 8,

        // No accessors for field names starting with _.
        _padding: 2,

        // Private bitint::U11 accessors.
        internal_number: 11,

        // Skip unused bits, in this case five bits.
        ..,

        // The two next-to-most significant bits with public
        // MyBitfieldEnum accessors.
        pub an_enum: 2 as MyBitfieldEnum,

        // Private bool accessors.
        high_bit_flag: 1 as bool,
    }

    pub enum MyBitfieldEnum: 2 {
        // Declare up to 2^width unit variants with optional
        // explicit discriminants.
        Three = 3,
        Zero = 0,
        One,

        // Generates `Unused2` to complete the enum.
        ..
    }
}

#[bitint_literals]
fn main() {
    // Use generated with_* methods to build bitfield structs.
    let x = MyBitfieldStruct::zero()
        .with_some_number(6_U3)
        .with_another_number(0xa5_U8)
        .with_internal_number(1025_U11)
        .with_an_enum(MyBitfieldEnum::One)
        .with_high_bit_flag(true);

    // Default accessors return bitints.
    assert_eq!(x.some_number(), 6_U3);
    assert_eq!(x.some_number().to_primitive(), 6);
    assert_eq!(x.another_number(), 0xa5_U8);
    assert_eq!(x.another_number().to_primitive(), 0xa5);
    assert_eq!(x.internal_number(), 1025_U11);
    assert_eq!(x.internal_number().to_primitive(), 1025);

    // Custom accessors return the chosen type, which must have Into
    // conversions to and from the default accessor bitint.
    assert_eq!(x.an_enum(), MyBitfieldEnum::One);
    assert_eq!(x.high_bit_flag(), true);

    // Zero-cost conversions to and from bitints and to primitive.
    // For bitfield structs:
    assert_eq!(
        x.to_bitint(),
        0b1_01_00000_10000000001_00_10100101_110_U32,
    );
    assert_eq!(
        x.to_primitive(),
        0b1_01_00000_10000000001_00_10100101_110,
    );
    assert_eq!(x, MyBitfieldStruct::from_bitint(0xa080252e_U32));
    // For bitfield enums:
    assert_eq!(MyBitfieldEnum::One.to_bitint(), 1_U2);
    assert_eq!(MyBitfieldEnum::One.to_primitive(), 1);
    assert_eq!(
        MyBitfieldEnum::One,
        MyBitfieldEnum::from_bitint(1_U2),
    );

    // Zero-cost conversion from primitive, only for primitive-sized
    // bitfield structs and enums.
    assert_eq!(x, MyBitfieldStruct::from_primitive(0xa080252e));
    bitfield! { enum MyU8Enum: 8 { X = 192, .. } }
    assert_eq!(MyU8Enum::X, MyU8Enum::from_primitive(192));

    // Bitfield enums optionally generate placeholder variants for
    // unused discriminants with `..`. The name is always "Unused"
    // followed by the discriminant value in base 10.
    assert_eq!(MyBitfieldEnum::Unused2.to_bitint(), 2_U2);
    assert_eq!(
        MyBitfieldEnum::Unused2,
        MyBitfieldEnum::from_bitint(2_U2),
    );
}
```
