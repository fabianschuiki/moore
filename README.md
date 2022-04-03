# moore

[![Build Status](https://travis-ci.org/fabianschuiki/moore.svg?branch=master)](https://travis-ci.org/fabianschuiki/moore)
[![Released API docs](https://docs.rs/moore/badge.svg)](https://docs.rs/moore)
[![Crates.io](https://img.shields.io/crates/v/moore.svg)](https://crates.io/crates/moore)
![Crates.io](https://img.shields.io/crates/l/moore)
[![dependency status](https://deps.rs/repo/github/fabianschuiki/moore/status.svg)](https://deps.rs/repo/github/fabianschuiki/moore)

Moore is a compiler for hardware description languages that outputs [llhd] assembly, with a focus on usability, clear error reporting, and completeness. Its goal is to act as a frontend for hardware design tools such as synthesizers, linters, or logical equivalence checkers.

## Usage

### Installation

You need a working [Rust installation](https://rustup.rs/) to build Moore. The project also depends on the [CIRCT project](https://github.com/llvm/circt) and transitively on MLIR and LLVM. To get a working binary, you generally want to ensure you have the `circt` and `circt/llvm` submodules checked out:

    git submodule update --init --recursive

And then follow these steps:

#### Build LLVM and MLIR

    mkdir -p circt/llvm/build
    pushd circt/llvm/build
    cmake ../llvm \
        -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_INSTALL_PREFIX=../install \
        -DLLVM_BUILD_EXAMPLES=OFF \
        -DLLVM_ENABLE_ASSERTIONS=ON \
        -DLLVM_ENABLE_BINDINGS=OFF \
        -DLLVM_ENABLE_OCAMLDOC=OFF \
        -DLLVM_ENABLE_PROJECTS=mlir \
        -DLLVM_INSTALL_UTILS=ON \
        -DLLVM_OPTIMIZED_TABLEGEN=ON \
        -DLLVM_TARGETS_TO_BUILD=""
    cmake --build . --target install
    popd

#### Build CIRCT

    mkdir -p circt/build
    pushd circt/build
    cmake .. \
        -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_INSTALL_PREFIX=../install \
        -DMLIR_DIR=$PWD/../llvm/install/lib/cmake/mlir \
        -DLLVM_DIR=$PWD/../llvm/install/lib/cmake/llvm \
        -DLLVM_ENABLE_ASSERTIONS=ON
    cmake --build . --target install
    popd

#### Build Moore

Set the following environment variables to indicate where your LLVM and CIRCT build is:

    export CIRCT_SYS_CIRCT_DIR=$PWD/circt
    export CIRCT_SYS_CIRCT_BUILD_DIR=$PWD/circt/install
    export CIRCT_SYS_LLVM_DIR=$PWD/circt/llvm
    export CIRCT_SYS_LLVM_BUILD_DIR=$PWD/circt/llvm/install

Use cargo to install pre-build Moore:

    cargo install moore
    
To use the self-build Moore:

    cargo build
    cargo install --path .

#### Development

For active development, you'll want to use the usual `check`, `build`, `run`, and `test` subcommands.

You may also find it useful to point the `*_BUILD_DIR` environment variables at the actual build directories (usually `circt/llvm/build` and `circt/build`), such that you don't need to re-install on every change to CIRCT or LLVM.

### Example

Assume the following input file:

    // foo.sv
    module hello_world;
    endmodule

To compile `foo.sv` and emit the corresponding LLHD assembly to standard output call moore with the file name and the module to elaborate (`-e` option):

    moore foo.sv -e hello_world

You can use [llhd-sim] to simulate the compiled module:

    moore foo.sv -e hello_world > foo.llhd
    llhd-sim foo.llhd

The -f parameter specifies the format of the output, and the options are `mlir|llhd`, 
- llhd is the format supported by the simulator llhd-sim written in rust 
- and mlir is the format supported by the simulator inherited from CIRCT

the -e parameter specifies the top-level module The name of the top-level module in the testbench above is updowncounter_tb; 
the -o parameter specifies the output file name; 
the remaining parameters are used as input files.

## Development

Moore is developed in this repository, but is separated into the following crates:

- `moore`: Top-level umbrella crate tying everything together
- `moore-common`: Common infrastructure used by SystemVerilog and VHDL
- `moore-derive`: Procedural macros
- `moore-svlog`: SystemVerilog implementation
- `moore-svlog-syntax`: SystemVerilog parser and AST implementation
- `moore-vhdl`: VHDL implementation
- `moore-vhdl-syntax`: VHDL parser and AST implementation
- `moore-circt`: Rust wrappers around the CIRCT API
- `moore-circt-sys`: Low-level language bindings to CIRCT

Some useful commands when working on moore:

    git submodule init
    git submodule update
    cargo check
    cargo test --all
    cargo run -- foo.sv -e foo
    scripts/test.py --debug -v
    scripts/test.py --debug -v <path-to-test-case>
    lit test -v

## Making a new Release

To create a new release, the individual sub-crates of the project have to be released in the reverse order outlined above. Follow this checklist:

1. Use `scripts/release_status.sh` to see an overview of moore/llhd crate versions used throughout the project
2. Update the version in all `Cargo.toml` files
3. Use `scripts/release_check.sh` to ensure that all crates have the same version as the root
5. Ensure cargo is happy: `cargo check`
4. Update the `CHANGELOG.md` file
5. Commit: `git commit -am "Bump version to X.Y.Z`
6. Tag: `git tag vX.Y.Z`
7. Publish all crates using `cargo publish` in reverse order


[llhd]: https://github.com/fabianschuiki/llhd
[llhd-sim]: https://github.com/fabianschuiki/llhd-sim
