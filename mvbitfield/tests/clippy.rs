use mvbitfield::prelude::*;

bitfield! {
    // This struct's field has the same primitive type as the struct. This used
    // to trip a Clippy lint in the generated code.
    #[lsb_first]
    pub struct MyStruct: 28 {
        pub my_field: 20 as U20,
        ..
    }
}
