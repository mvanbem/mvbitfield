use mvbitfield::prelude::*;

bitfield! {
    pub enum WithinBounds: 10 { .. }

    pub enum TooWide: 11 { .. }

    pub enum FarTooWide: 128 { .. }

    pub enum CatastrophicallyTooWide: 1048576 { .. }
}

fn main() {}
