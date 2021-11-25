#!/bin/bash
set -e

mkdir -p circt/llvm/build
cd circt/llvm/build
cmake ../llvm \
    -DCMAKE_BUILD_TYPE=Release \
    -DLLVM_BUILD_EXAMPLES=OFF \
    -DLLVM_ENABLE_ASSERTIONS=ON \
    -DLLVM_ENABLE_BINDINGS=OFF \
    -DLLVM_ENABLE_OCAMLDOC=OFF \
    -DLLVM_ENABLE_PROJECTS=mlir \
    -DLLVM_INSTALL_UTILS=ON \
    -DLLVM_OPTIMIZED_TABLEGEN=ON \
    -DLLVM_TARGETS_TO_BUILD=""

cmake --build . -- -j$(nproc)
