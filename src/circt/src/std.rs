// Copyright (c) 2016-2021 Fabian Schuiki

use crate::mlir::DialectHandle;
use circt_sys::*;

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { mlirGetDialectHandle__std__() })
}
