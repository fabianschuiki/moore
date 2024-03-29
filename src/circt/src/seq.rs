// Copyright (c) 2016-2021 Fabian Schuiki

use crate::mlir::DialectHandle;

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { crate::sys::mlirGetDialectHandle__seq__() })
}
