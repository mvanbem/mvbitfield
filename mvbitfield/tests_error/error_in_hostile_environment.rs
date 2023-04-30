mod bitint {}
mod core {}
mod mvbitfield {}

::mvbitfield::bitfield! {
    pub struct MyStruct: 3 {
        pub x: 4,
    }
}

fn main() {}
