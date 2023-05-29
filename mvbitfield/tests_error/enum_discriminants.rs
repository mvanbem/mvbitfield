use mvbitfield::prelude::*;

bitfield! {
    pub enum ExplicitOutOfRange: 4 {
        A = 16,
    }

    pub enum ImplicitOutOfRange: 5 {
        A = 31,
        B,
    }

    pub enum RepeatedDiscriminant: 1 {
        Zero,
        One,
        X = 0,
    }

    pub enum MiddleGapWithoutPlaceholder: 2 {
        Zero,
        Two = 2,
        Three,
    }

    pub enum EndGapWithoutPlaceholder: 2 {
        Zero,
        One,
        Two,
    }

    pub enum ThreeUnused: 2 {
        Zero,
    }

    pub enum FourUnused: 3 {
        Zero,
        One,
        Two,
        Three,
    }

    pub enum FiveUnused: 3 {
        Zero,
        One,
        Two,
    }
}

fn main() {}
