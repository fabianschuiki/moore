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


[1]: https://github.com/pulp-platform/pulpino
[2]: https://github.com/fabianschuiki/llhd
