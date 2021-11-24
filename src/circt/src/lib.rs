// Copyright (c) 2016-2021 Fabian Schuiki

/// Define an operation.
macro_rules! def_operation {
    ($name:ident, $operation_name:expr) => {
        #[derive(Clone, Copy)]
        pub struct $name(MlirOperation);

        impl WrapRaw for $name {
            type RawType = MlirOperation;
            fn from_raw(raw: MlirOperation) -> Self {
                Self(raw)
            }
            fn raw(&self) -> MlirOperation {
                self.0
            }
        }

        impl OperationExt for $name {
            fn operation_name() -> &'static str {
                $operation_name
            }
        }
    };
}

/// Define an operation with a single result.
macro_rules! def_operation_single_result {
    ($name:ident, $operation_name:expr) => {
        def_operation!($name, $operation_name);

        impl Into<Value> for $name {
            fn into(self) -> Value {
                self.result(0)
            }
        }
    };
}

/// Define a unary operation with the result type inherited from the operand.
#[allow(unused_macros)]
macro_rules! def_simple_unary_operation {
    ($name:ident, $operation_name:expr) => {
        def_operation_single_result!($name, $operation_name);

        impl $name {
            pub fn new(builder: &mut Builder, arg: Value) -> Self {
                builder.build_with(|_, state| {
                    state.add_operand(arg);
                    state.add_result(arg.ty());
                })
            }
        }
    };
}

/// Define a binary operation with the result type inherited from the first
/// operand.
macro_rules! def_simple_binary_operation {
    ($name:ident, $operation_name:expr) => {
        def_operation_single_result!($name, $operation_name);

        impl $name {
            pub fn new(builder: &mut Builder, lhs: Value, rhs: Value) -> Self {
                builder.build_with(|_, state| {
                    state.add_operand(lhs);
                    state.add_operand(rhs);
                    state.add_result(lhs.ty());
                })
            }
        }
    };
}

/// Define a binary operation with an explicit result type.
macro_rules! def_binary_operation_explicit_result {
    ($name:ident, $operation_name:expr) => {
        def_operation_single_result!($name, $operation_name);

        impl $name {
            pub fn new(builder: &mut Builder, ty: Type, lhs: Value, rhs: Value) -> Self {
                builder.build_with(|_, state| {
                    state.add_operand(lhs);
                    state.add_operand(rhs);
                    state.add_result(ty);
                })
            }
        }
    };
}

pub mod builtin;
pub mod comb;
pub mod hw;
pub mod llhd;
pub mod mlir;
pub mod seq;
pub mod std;

pub use builtin::*;

pub mod sys {
    pub use circt_sys::*;
}

pub mod prelude {
    pub use crate::llhd::EntityLike as _;
    pub use crate::mlir::{
        OperationExt as _, SingleBlockOp as _, SingleRegionOp as _, WrapRaw as _,
    };
}

mod crate_prelude {
    pub use crate::mlir::*;
    pub use crate::prelude::*;
    pub use crate::sys::*;
    pub use num::{BigInt, BigRational, One, ToPrimitive, Zero};
}
