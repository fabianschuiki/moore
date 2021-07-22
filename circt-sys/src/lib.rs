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
