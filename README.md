# moore

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
    - `always_{ff,latch,comb}` -> `always`
- typecheck and evaluate const exprs
- specialize generic instances
- assign and check types (can be one step)
- lower to LLHD
- link and emit output file


[1]: https://github.com/pulp-platform/pulpino
[2]: https://github.com/fabianschuiki/llhd
