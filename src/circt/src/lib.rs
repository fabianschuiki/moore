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
    pub use crate::mlir::{OperationExt as _, WrapRaw as _};
}

mod crate_prelude {
    pub use crate::mlir::*;
    pub use crate::prelude::*;
    pub use crate::sys::*;
    pub use num::{BigInt, BigRational, One, ToPrimitive, Zero};
}
