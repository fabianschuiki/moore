#include "wrapper.h"
#include "mlir/CAPI/IR.h"
#include "mlir/CAPI/Support.h"
#include "mlir/IR/BuiltinTypes.h"

using namespace llvm;
using namespace mlir;

MlirAttribute mlirIntegerAttrGetFromString(MlirType type, MlirStringRef value) {
  auto intType = unwrap(type).cast<IntegerType>();
  auto intWidth = intType.getWidth();
  auto valueStr = unwrap(value);
  auto tmpWidth = std::max<size_t>(intWidth, (valueStr.size() - 1) * 64 / 22);
  return wrap(
      IntegerAttr::get(intType, APInt(tmpWidth, valueStr, 10).trunc(intWidth)));
}

bool mlirLocationIsFileLineCol(MlirLocation loc) {
  return unwrap(loc).isa<FileLineColLoc>();
}

MlirStringRef mlirFileLineColLocGetFilename(MlirLocation loc) {
  return wrap(unwrap(loc).cast<FileLineColLoc>().getFilename().strref());
}

unsigned mlirFileLineColLocGetLine(MlirLocation loc) {
  return unwrap(loc).cast<FileLineColLoc>().getLine();
}

unsigned mlirFileLineColLocGetColumn(MlirLocation loc) {
  return unwrap(loc).cast<FileLineColLoc>().getColumn();
}
