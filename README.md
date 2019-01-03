# moore

[![Build Status](https://travis-ci.org/fabianschuiki/moore.svg?branch=master)](https://travis-ci.org/fabianschuiki/moore)
[![Released API docs](https://docs.rs/moore/badge.svg)](https://docs.rs/moore)
[![Crates.io](https://img.shields.io/crates/v/moore.svg)](https://crates.io/crates/moore)

Moore is a compiler for hardware description languages that outputs [LLHD][2], with a focus on usability, clear error reporting, and completeness.


## Roadmap

1. [x] Parse the entire source code of [PULPino][1]
2. [ ] Elaborate and link PULPino
3. [ ] Generate LLHD code for PULPino
4. [ ] Pass PULPino continuous integration testbenches


## Compile Flow

Compilation
- parse input file(s)
- serialize AST to disk

Elaboration
- load ASTs from disk
- renumber nodes
- resolve names
- lower to HIR
    - apply default values
    - merge ANSI and non-ANSI ports
    - split ports into port decl and var/net decl
    - split net decl assignments into net decl and continuous assignment
    - `always_{ff,latch,comb}` -> `always`
    - flatten nested design elements and sort hierarchy items
- assign and check types (can be one step)
- evaluate const exprs
- specialize generic instances
- lower to MIR
    - evaluate generate constructs
    - determine scheduling
- perform static analyses (future work)
- lower to LLHD
- link and emit output file

### Lowering to HIR

Lowering to HIR resolves syntactic sugar and applies default values. Additionally, the following steps are performed:

- determine port kind, direction, and type of ANSI ports
- pair non-ANSI ports with port and var/net decls in the module body
- merge ANSI and non-ANSI ports into one common port structure


[1]: https://github.com/pulp-platform/pulpino
[2]: https://github.com/fabianschuiki/llhd
