// Copyright (c) 2016-2021 Fabian Schuiki

use crate::crate_prelude::*;

def_operation!(ModuleOp, "builtin.module");
def_operation!(FuncOp, "builtin.func");

impl ModuleOp {
    /// Create a new module.
    pub fn new(cx: Context) -> Self {
        unsafe {
            let mut state = mlirOperationStateGet(
                mlirStringRefCreateFromStr(Self::operation_name()),
                mlirLocationUnknownGet(cx.raw()),
            );
            let region = mlirRegionCreate();
            mlirRegionAppendOwnedBlock(region, mlirBlockCreate(0, std::ptr::null()));
            mlirOperationStateAddOwnedRegions(&mut state, 1, [region].as_ptr());
            Self(mlirOperationCreate(&mut state))
        }
    }
}

impl SingleRegionOp for ModuleOp {}
impl SingleBlockOp for ModuleOp {}

pub struct FunctionBuilder<'a> {
    name: &'a str,
    args: Vec<(&'a str, Type)>,
    results: Vec<(&'a str, Type)>,
}

impl SingleRegionOp for FuncOp {}

impl<'a> FunctionBuilder<'a> {
    pub fn new(name: &'a str) -> Self {
        Self {
            name,
            args: vec![],
            results: vec![],
        }
    }

    /// Add an argument.
    pub fn add_arg(&mut self, name: &'a str, ty: Type) -> &mut Self {
        self.args.push((name, ty));
        self
    }

    /// Add a result.
    pub fn add_result(&mut self, name: &'a str, ty: Type) -> &mut Self {
        self.results.push((name, ty));
        self
    }

    /// Build a function.
    pub fn build(&mut self, builder: &mut Builder) -> FuncOp {
        builder.build_with(|builder, state| {
            let arg_types = self.args.iter().map(|(_, ty)| *ty);
            let result_types = self.results.iter().map(|(_, ty)| *ty);
            let mlir_arg_types: Vec<MlirType> = arg_types.clone().map(|x| x.raw()).collect();
            // let mlir_result_types: Vec<MlirType> = result_types.clone().map(|x| x.raw()).collect();

            state.add_attribute("sym_name", get_string_attr(builder.cx, self.name));
            state.add_attribute(
                "type",
                get_type_attr(get_function_type(builder.cx, arg_types, result_types)),
            );

            unsafe {
                let region = mlirRegionCreate();
                mlirRegionAppendOwnedBlock(
                    region,
                    mlirBlockCreate(mlir_arg_types.len() as _, mlir_arg_types.as_ptr()),
                );
                state.add_region(region);
            }
        })
    }
}
