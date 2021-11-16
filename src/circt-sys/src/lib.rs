// Copyright (c) 2016-2021 Fabian Schuiki

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

pub unsafe fn mlirStringRefCreateFromStr(s: impl AsRef<str>) -> MlirStringRef {
    let s = s.as_ref().as_bytes();
    MlirStringRef {
        data: s.as_ptr() as *const _,
        length: s.len() as size_t,
    }
}

pub unsafe fn mlirStringRefToStr<R>(s: MlirStringRef, f: impl Fn(&str) -> R) -> R {
    f(std::str::from_utf8(std::slice::from_raw_parts(
        s.data as *const _,
        s.length as usize,
    ))
    .expect("utf8 string"))
}
