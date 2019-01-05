# moore

[![Build Status](https://travis-ci.org/fabianschuiki/moore.svg?branch=master)](https://travis-ci.org/fabianschuiki/moore)
[![Released API docs](https://docs.rs/moore/badge.svg)](https://docs.rs/moore)
[![Crates.io](https://img.shields.io/crates/v/moore.svg)](https://crates.io/crates/moore)

Moore is a compiler for hardware description languages that outputs [llhd] assembly, with a focus on usability, clear error reporting, and completeness. Its goal is to act as a frontend for hardware design tools such as synthesizers, linters, or logical equivalence checkers.

## Usage

### Installation

You need a working [Rust installation](https://rustup.rs/). Use cargo to install moore:

    cargo install moore

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

## Development

Moore is developed in this repository, but is separated into the following crates:

- `moore`: Top-level umbrella crate tying everything together
- `moore-svlog`: SystemVerilog implementation
- `moore-svlog-syntax`: SystemVerilog parser and AST implementation
- `moore-vhdl`: VHDL implementation
- `moore-vhdl-syntax`: VHDL parser and AST implementation

Some useful commands when working on moore:

    cargo check
    cargo test --all
    cargo run -- foo.sv -e foo

[llhd]: https://github.com/fabianschuiki/llhd
[llhd-sim]: https://github.com/fabianschuiki/llhd-sim
