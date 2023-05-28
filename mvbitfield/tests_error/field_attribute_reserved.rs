use mvbitfield::prelude::*;

bitfield! {
    struct MyStruct: 32 {
        #[this_is_not_a_doc_attribute]
        x: 32,
    }

    struct EnforcedWithUnderscore: 32 {
        #[this_is_also_not_a_doc_attribute]
        _x: 32,
    }
}

fn main() {}
