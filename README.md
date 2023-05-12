# mvbitfield

A bitfield library for Rust.

`mvbitfield` generates bitfield struct types that can insert and extract
bit-aligned fields.

Bitfield structs serve roughly the same use cases as C/C++ structs with
bit-field members.

The generated bitfield structs are:

- **Endian-insensitive**, packing fields within an integer rather than across
  bytes or array elements.
- **Flexible and type-safe** with optional user-defined field accessor types.
- **Suitable for FFI and memory-mapped I/O** with care, as always.

## Demo

```rust
// Recommended, but not required. The mvbitfield prelude includes the bitint
// prelude.
use mvbitfield::prelude::*;

bitfield! {
    #[lsb_first]               // Field packing order.
    #[derive(PartialOrd, Ord)] // Other attributes are passed through.
    pub struct MyBitfieldStruct: 32 {
        // The lowest 3 bits with public bitint::U3 accessors.
        pub some_number: 3,

        // The next 8 bits with public bitint::U8 accessors.
        pub another_number: 8,

        // No accessors for field names starting with _.
        _padding: 2,

        // Private bitint::U11 accessors.
        internal_number: 11,

        // Skip unused bits, in this case 7 bits.
        ..,

        // Private bool accessors.
        high_bit_flag: 1 as bool,
    }
}

#[bitint_literals]
fn main() {
    // Use generated with_* methods to build bitfield structs.
    let x = MyBitfieldStruct::zero()
        .with_some_number(6_U3)
        .with_another_number(0xa5_U8)
        .with_internal_number(1025_U11)
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
    assert_eq!(x.high_bit_flag(), true);

    // Zero-cost conversions to and from bitints and to primitive.
    assert_eq!(x.to_bitint(), 0b1_0000000_10000000001_00_10100101_110_U32);
    assert_eq!(x.to_primitive(), 0b1_0000000_10000000001_00_10100101_110);
    assert_eq!(x, MyBitfieldStruct::from_bitint(0x8080252e_U32));

    // Zero-cost conversion from primitive, only for primitive-sized
    // bitfield structs.
    assert_eq!(x, MyBitfieldStruct::from_primitive(0x8080252e));
}
```
