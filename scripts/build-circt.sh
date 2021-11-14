#!/bin/bash
set -e

[ -z "$MOORE_CIRCT_BUILD_TYPE" ] && export MOORE_CIRCT_BUILD_TYPE=Debug

cd "$(dirname $0)/.."

pushd circt/llvm
mkdir -p build && cd build
cmake -G Ninja ../llvm \
    -Wno-dev \
    -DLLVM_ENABLE_PROJECTS="mlir" \
    -DLLVM_TARGETS_TO_BUILD="" \
    -DCMAKE_BUILD_TYPE=$MOORE_CIRCT_BUILD_TYPE
ninja -k0
popd

pushd circt
mkdir -p build && cd build
cmake -G Ninja .. \
    -Wno-dev \
    -DMLIR_DIR=$PWD/../llvm/build/lib/cmake/mlir \
    -DLLVM_DIR=$PWD/../llvm/build/lib/cmake/llvm \
    -DCMAKE_BUILD_TYPE=$MOORE_CIRCT_BUILD_TYPE
ninja -k0
popd
