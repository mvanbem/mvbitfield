mod bitint {}
mod core {}
mod mvbitfield {}

::mvbitfield::bitfield! {
    #[msb_first]
    pub struct MyStruct: 16 {
        pub high_bit: 1 as bool,
        pub next_two_bits: 2,
        ..,
        pub a_low_bit: 1,
        pub last_three_bits: 3,
    }
}
