use mvbitfield::prelude::*;

mod custom {
    use mvbitfield::prelude::*;

    pub struct MyPrimitive(u8);

    impl MyPrimitive {
        pub fn new(value: u8) -> Self {
            Self(value)
        }
    }

    impl From<U8> for MyPrimitive {
        fn from(value: U8) -> Self {
            Self(value.into())
        }
    }

    impl From<MyPrimitive> for U8 {
        fn from(value: MyPrimitive) -> Self {
            value.0.into()
        }
    }

    pub struct MyBitint(U3);

    impl MyBitint {
        pub fn new(value: U3) -> Self {
            Self(value)
        }
    }

    impl From<U3> for MyBitint {
        fn from(value: U3) -> Self {
            Self(value)
        }
    }

    impl From<MyBitint> for U3 {
        fn from(value: MyBitint) -> Self {
            value.0
        }
    }
}

bitfield! {
    #[lsb_first]
    struct MyStruct: 28 {
        implicit: 5,
        primitive: 8 as u8,
        explicit: 4 as U4,
        user_primitive: 8 as custom::MyPrimitive,
        user_bitint: 3 as custom::MyBitint,
    }
}

#[bitint_literals]
#[test]
fn test_packing() {
    assert_eq!(
        MyStruct::zero().with_implicit(31_U5).to_primitive(),
        0b000_00000000_0000_00000000_11111,
    );
    assert_eq!(
        MyStruct::zero().with_primitive(255).to_primitive(),
        0b000_00000000_0000_11111111_00000,
    );
    assert_eq!(
        MyStruct::zero().with_explicit(15_U4).to_primitive(),
        0b000_00000000_1111_00000000_00000,
    );
    assert_eq!(
        MyStruct::zero()
            .with_user_primitive(custom::MyPrimitive::new(255))
            .to_primitive(),
        0b000_11111111_0000_00000000_00000,
    );
    assert_eq!(
        MyStruct::zero()
            .with_user_bitint(custom::MyBitint::new(7_U3))
            .to_primitive(),
        0b111_00000000_0000_00000000_00000,
    );
}
