# Release 0.2.0 (2023-05-28)

## Enhancements

* New feature: bitfield enums.
* Added doc comment support for bitfield struct field declarations.

## Breaking Changes

* Renamed `BitfieldStruct` trait to `Bitfield`.
* Attributes other than `doc` are now rejected on bitfield struct field
  declarations.

# Release 0.1.1 (2023-05-11)

Fixed a formatting error in the crates.io readme.

# Release 0.1.0 (2023-05-11)

Initial release featuring the `bitfield!` macro and bitfield structs.
