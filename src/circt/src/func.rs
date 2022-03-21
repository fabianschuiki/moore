// Copyright (c) 2016-2021 Fabian Schuiki

use crate::crate_prelude::*;

pub fn dialect() -> DialectHandle {
    DialectHandle::from_raw(unsafe { mlirGetDialectHandle__func__() })
}

def_operation!(FuncOp, "func.func");
def_operation!(CallOp, "func.call");
def_operation!(ReturnOp, "func.return");

pub struct FunctionBuilder<'a> {
    name: &'a str,
    args: Vec<(String, Type)>,
    results: Vec<(String, Type)>,
}

impl SingleRegionOp for FuncOp {}

impl FuncOp {
    /// Get the number of arguments.
    pub fn num_arguments(&self) -> usize {
        unsafe { mlirBlockGetNumArguments(self.first_block()) as usize }
    }

    /// Get an argument by index.
    pub fn argument(&self, index: usize) -> Value {
        unsafe { Value::from_raw(mlirBlockGetArgument(self.first_block(), index as _)) }
    }

    /// Get an iterator over all arguments.
    pub fn arguments(&self) -> Box<dyn Iterator<Item = Value> + '_> {
        Box::new((0..self.num_arguments()).map(move |i| self.argument(i)))
    }
}

impl<'a> FunctionBuilder<'a> {
    pub fn new(name: &'a str) -> Self {
        Self {
            name,
            args: vec![],
            results: vec![],
        }
    }

    /// Add an argument.
    pub fn add_arg(&mut self, name: Option<String>, ty: Type) -> &mut Self {
        self.args.push((name.unwrap_or("".to_string()), ty));
        self
    }

    /// Add a result.
    pub fn add_result(&mut self, name: Option<String>, ty: Type) -> &mut Self {
        self.results.push((name.unwrap_or("".to_string()), ty));
        self
    }

    /// Build a function.
    pub fn build(&mut self, builder: &mut Builder) -> FuncOp {
        builder.build_with(|builder, state| {
            let arg_types = self.args.iter().map(|(_, ty)| *ty);
            let result_types = self.results.iter().map(|(_, ty)| *ty);
            let mlir_arg_types: Vec<MlirType> = arg_types.clone().map(|x| x.raw()).collect();
            // let mlir_result_types: Vec<MlirType> = result_types.clone().map(|x| x.raw()).collect();
            // let arg_names: Vec<Attribute> = self
            //     .args
            //     .iter()
            //     .map(|(name, _)| get_string_attr(builder.cx, name))
            //     .collect();

            state.add_attribute("sym_name", get_string_attr(builder.cx, self.name));
            state.add_attribute(
                "function_type",
                get_type_attr(get_function_type(builder.cx, arg_types, result_types)),
            );
            // state.add_attribute("arg_names", get_array_attr(builder.cx, arg_names));

            unsafe {
                let region = mlirRegionCreate();
                let locations = vec![Location::unknown(builder.cx).raw(); mlir_arg_types.len()];
                mlirRegionAppendOwnedBlock(
                    region,
                    mlirBlockCreate(
                        mlir_arg_types.len() as _,
                        mlir_arg_types.as_ptr(),
                        locations.as_ptr(),
                    ),
                );
                state.add_region(region);
            }
        })
    }
}

impl CallOp {
    /// Create a new call.
    pub fn new(
        builder: &mut Builder,
        callee: &str,
        args: impl IntoIterator<Item = Value>,
        results: impl IntoIterator<Item = Type>,
    ) -> Self {
        builder.build_with(|builder, state| {
            let _num_args = args.into_iter().map(|v| state.add_operand(v)).count();
            let _num_results = results.into_iter().map(|v| state.add_result(v)).count();
            state.add_attribute("callee", get_flat_symbol_ref_attr(builder.cx, callee));
        })
    }
}

impl ReturnOp {
    /// Create a new return.
    pub fn new(builder: &mut Builder, values: impl IntoIterator<Item = Value>) -> Self {
        builder.build_with(|_, state| {
            for v in values {
                state.add_operand(v);
            }
        })
    }
}
