#!/bin/bash
set -e

mkdir -p circt/build
cd circt/build
cmake .. \
    -DCMAKE_BUILD_TYPE=Release \
    -DMLIR_DIR=$PWD/../llvm/build/lib/cmake/mlir \
    -DLLVM_DIR=$PWD/../llvm/build/lib/cmake/llvm \
    -DLLVM_ENABLE_ASSERTIONS=ON

cmake --build . -- -j$(nproc)
