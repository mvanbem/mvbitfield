use core::convert::Infallible;

use mvbitfield::prelude::*;

bitfield! {
    struct FourBitStruct: 4 { .. }

    #[msb_first]
    struct MyStruct: 32 {
        flag_width_mismatch: 2 as bool,
        bitint_width_mismatch: 3 as U4,
        struct_width_mismatch: 5 as FourBitStruct,
        unit: 3 as (),
        never: 2 as Infallible,
        ..
    }
}

fn main() {}
