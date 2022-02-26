#pragma once
#include "circt-c/Dialect/Comb.h"
#include "circt-c/Dialect/HW.h"
#include "circt-c/Dialect/LLHD.h"
#include "circt-c/Dialect/Seq.h"
#include "mlir-c/AffineExpr.h"
#include "mlir-c/AffineMap.h"
#include "mlir-c/BuiltinAttributes.h"
#include "mlir-c/BuiltinTypes.h"
#include "mlir-c/Conversion.h"
#include "mlir-c/Debug.h"
#include "mlir-c/Diagnostics.h"
#include "mlir-c/Dialect/Async.h"
#include "mlir-c/Dialect/ControlFlow.h"
#include "mlir-c/Dialect/GPU.h"
#include "mlir-c/Dialect/LLVM.h"
#include "mlir-c/Dialect/Linalg.h"
#include "mlir-c/Dialect/SCF.h"
#include "mlir-c/Dialect/Shape.h"
#include "mlir-c/Dialect/SparseTensor.h"
#include "mlir-c/Dialect/Standard.h"
#include "mlir-c/Dialect/Tensor.h"
#include "mlir-c/ExecutionEngine.h"
#include "mlir-c/IR.h"
#include "mlir-c/IntegerSet.h"
#include "mlir-c/Pass.h"
#include "mlir-c/Registration.h"
#include "mlir-c/Support.h"
#include "mlir-c/Transforms.h"

#ifdef __cplusplus
extern "C" {
#endif

/// Creates an integer attribute of the given type by parsing the given string
/// into an integer value.
MLIR_CAPI_EXPORTED MlirAttribute
mlirIntegerAttrGetFromString(MlirType type, MlirStringRef value);

//===----------------------------------------------------------------------===//
// Location API Extensions
//===----------------------------------------------------------------------===//

MLIR_CAPI_EXPORTED bool mlirLocationIsFileLineCol(MlirLocation);
MLIR_CAPI_EXPORTED MlirStringRef mlirFileLineColLocGetFilename(MlirLocation);
MLIR_CAPI_EXPORTED unsigned mlirFileLineColLocGetLine(MlirLocation);
MLIR_CAPI_EXPORTED unsigned mlirFileLineColLocGetColumn(MlirLocation);

#ifdef __cplusplus
}
#endif
