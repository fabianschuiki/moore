// Copyright (c) 2016-2021 Fabian Schuiki

//! An MLIR type.

use crate::crate_prelude::*;
use std::fmt::{Debug, Display};

/// An MLIR type.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Type(MlirType);

impl Type {
    /// Get the type's MLIR context.
    pub fn context(&self) -> Context {
        Context::from_raw(unsafe { mlirTypeGetContext(self.raw()) })
    }
}

impl WrapRaw for Type {
    type RawType = MlirType;
    fn from_raw(raw: MlirType) -> Self {
        Self(raw)
    }
    fn raw(&self) -> MlirType {
        self.0
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        unsafe {
            mlirTypePrint(
                self.raw(),
                Some(super::print_formatter_callback),
                f as *const _ as *mut _,
            )
        };
        Ok(())
    }
}

impl Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

/// Check if a type is an MLIR integer type.
pub fn is_integer_type(ty: Type) -> bool {
    unsafe { mlirTypeIsAInteger(ty.raw()) }
}

/// Create a new integer type of a given width.
pub fn get_integer_type(cx: Context, bitwidth: usize) -> Type {
    Type::from_raw(unsafe { mlirIntegerTypeGet(cx.raw(), bitwidth as _) })
}

/// Return the width of an integer type.
pub fn integer_type_width(ty: Type) -> usize {
    unsafe { mlirIntegerTypeGetWidth(ty.raw()) as _ }
}

/// Create a new function type.
pub fn get_function_type(
    cx: Context,
    inputs: impl IntoIterator<Item = Type>,
    results: impl IntoIterator<Item = Type>,
) -> Type {
    let inputs: Vec<MlirType> = inputs.into_iter().map(|x| x.raw()).collect();
    let results: Vec<MlirType> = results.into_iter().map(|x| x.raw()).collect();
    Type::from_raw(unsafe {
        mlirFunctionTypeGet(
            cx.raw(),
            inputs.len() as _,
            inputs.as_ptr(),
            results.len() as _,
            results.as_ptr(),
        )
    })
}

/// Return the number of inputs of a function type.
pub fn function_type_num_inputs(ty: Type) -> usize {
    unsafe { mlirFunctionTypeGetNumInputs(ty.raw()) as _ }
}

/// Return the number of results of a function type.
pub fn function_type_num_results(ty: Type) -> usize {
    unsafe { mlirFunctionTypeGetNumResults(ty.raw()) as _ }
}

/// Return an input of a function type.
pub fn function_type_input(ty: Type, index: usize) -> Type {
    Type::from_raw(unsafe { mlirFunctionTypeGetInput(ty.raw(), index as _) })
}

/// Return a result of a function type.
pub fn function_type_result(ty: Type, index: usize) -> Type {
    Type::from_raw(unsafe { mlirFunctionTypeGetResult(ty.raw(), index as _) })
}

/// Return the inputs of a function type.
pub fn function_type_inputs(ty: Type) -> impl Iterator<Item = Type> {
    (0..function_type_num_inputs(ty)).map(move |i| function_type_input(ty, i))
}

/// Return the results of a function type.
pub fn function_type_results(ty: Type) -> impl Iterator<Item = Type> {
    (0..function_type_num_results(ty)).map(move |i| function_type_result(ty, i))
}
