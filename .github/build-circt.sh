#!/bin/bash
set -e

mkdir -p circt/build
mkdir -p circt/install
cd circt/build
cmake .. \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_INSTALL_PREFIX=../install \
    -DMLIR_DIR=$PWD/../llvm/install/lib/cmake/mlir \
    -DLLVM_DIR=$PWD/../llvm/install/lib/cmake/llvm \
    -DLLVM_ENABLE_ASSERTIONS=ON

cmake --build . --target install -- -j$(nproc)
