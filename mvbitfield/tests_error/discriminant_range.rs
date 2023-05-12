use mvbitfield::prelude::*;

bitfield! {
    pub enum ExplicitOutOfRange: 4 {
        A = 16,
    }

    pub enum ImplicitOutOfRange: 5 {
        A = 31,
        B,
    }
}

fn main() {}
