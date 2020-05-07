# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/), and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased
### Added
- Add parsing support for `assert final` assertions (#139)
- Add parsing support for `default disable` statements (#140)
- Add codegen support for case/wildcard equality operators (#147)

### Fixed
- Fix sign casts (#138)
- Fix parsing of import declarations in module headers (#136)
- Fix non-constant initial expressions in variabel declarations

## 0.7.0 - 2020-04-30
### Added
- Add the `--syntax` option to only syntax-check input files.
- Add support for `__FILE__` and `__LINE__` directives.
- Add support for `resetall` directive.
- Add support for `celldefine` and `endcelldefine` directives.
- Add support for `default_nettype` directive.
- Add support for `begin_keywords` and `end_keywords` directives.
- Add support for `line` directive.
- Add support for `unconnected_drive` and `nounconnected_drive` directives.
- Add full support for ANSI and non-ANSI port lists. ([#128](https://github.com/fabianschuiki/moore/issues/128))
- Add the `-Vports` verbosity option.

### Fixed
- Fix parsing of keywords `implements`, `interconnect`, `nettype`, `soft`.

## 0.6.0 - 2020-01-26
### Added
- Add bit-vec dependency.
- Add support for `x` and `z` bits in literals.
- Add support for `casex` and `casez` statements.
- Add shadow variables for blocking assignments.
- Interpret `reg` type as `logic`.

### Changed
- Improved output of `-Vtypes` verbosity option.
- Improve type checking quality with separate queries.

### Fixed
- Parent relationship of HIR nodes lowered from AST.
- Type of part-selects now reflects length of selection.
- Use operation type for comparisons and inside expressions.
- Don't consider type context for comparison operations.
- Fix implicit boolean casts in if, for, while, do/while, and event statements.
- Fix `$unsigned` and `$signed` type checking.
- Fix right-hand side casting in assignments.
- Fix implicit array unpacking.
- Fix code generated for concatenation.
- Fix nested `ifdef` in preprocessor.
- Fix parsing of delays on net declarations.
- Fix parsing of unparenthesized identifiers as delay value (following `#`).
- Fix parsing of DPI imports.
- Fix parsing of elaboration system tasks.
- Fix implicitly-typed variables.

## 0.5.0 - 2019-10-24
### Added
- Parsing of `timeunit` and `timeprecision` statements. ([#92](https://github.com/fabianschuiki/moore/issues/92))
- Parsing of `inside` expressions. ([#93](https://github.com/fabianschuiki/moore/issues/93))
- Support for the `**` operators. ([#94](https://github.com/fabianschuiki/moore/issues/94))
- Support for the `::` operator.
- Support for the `case` statement.
- Parse cast expressions.
- Accept ``` `` ```, `` `\ ``, and `` `" `` in preprocessor.
- Parse optional lifetime specifiers after `task` or `function`.
- Support for enum types. ([#79](https://github.com/fabianschuiki/moore/issues/79))
- Support for package declarations.
- Support for the `$signed` and `$unsigned` builtin functions.
- Support auto-connected and unconnected ports.
- Support for the `{...}` concatenation and `{N{...}}` repetition operators.
- Add `-On` switch to control optimization level.
- Add MIR for rvalues and lvalues. ([#104](https://github.com/fabianschuiki/moore/issues/104))
- Support for the ``` `undef ``` and ``` `undefineall ``` directives.
- Inline the [salsa](https://github.com/fabianschuiki/salsa/tree/moore) crate.

### Changed
- Update llhd to v0.9.0.
- Support for the `ty'(expr)` cast expression.
- Increase minimum rustc version to 1.36.

### Fixed
- Continuous assignments resolve in epsilon time. ([#89](https://github.com/fabianschuiki/moore/issues/89))
- Ternary operator now also supported at entitiy-level.
- Fix underscores in preprocessor macros.
- Fix parsing of size cast expressions, e.g. `32'(x)`. ([#113](https://github.com/fabianschuiki/moore/issues/113))
- Recognize `*.vh` files as verilog source code.

## 0.4.0 - 2019-02-19
### Added
- Support for variable declarations. ([#70](https://github.com/fabianschuiki/moore/issues/70))
- Support for struct types. ([#76](https://github.com/fabianschuiki/moore/issues/76))
- Support for packed arrays. ([#75](https://github.com/fabianschuiki/moore/issues/75))
- Support for the `*`, `/`, `%`, `<<`, `<<<`, `>>`, and `>>>` operators.
- Support for the `$clog2` and `$bits` builtin functions. ([#81](https://github.com/fabianschuiki/moore/issues/81), [#88](https://github.com/fabianschuiki/moore/issues/88))
- Support for non-blocking assignments with and without delay. ([#82](https://github.com/fabianschuiki/moore/issues/82))
- Support for based integer literals, and `'0`, and `'1`. ([#84](https://github.com/fabianschuiki/moore/issues/84))
- Support for the ternary operator in processes and functions. ([#83](https://github.com/fabianschuiki/moore/issues/83))
- Support for the unary `+`, `-`, `&`, `~&`, `|`, `~|`, `^`, and `^~` operators. ([#86](https://github.com/fabianschuiki/moore/issues/86))
- Support for `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, `<<<=`, `>>=`, and `>>>=` assignments. ([#87](https://github.com/fabianschuiki/moore/issues/87))

### Fixed
- Fix blocking assignments, making them actually block. ([#78](https://github.com/fabianschuiki/moore/issues/78))
- Fix variables with implicit types failing to infer their type.
- Fix error when parameters or genvars are used in process. ([#85](https://github.com/fabianschuiki/moore/issues/85))

### Changed
- Update llhd to v0.5.0.
- Make emitted process names more descriptive.

### Removed
- Remove obsolete code in the svlog syntax crate. ([#80](https://github.com/fabianschuiki/moore/issues/80))

## 0.3.0 - 2019-02-01
### Added
- Support for parameter declarations. ([#71](https://github.com/fabianschuiki/moore/issues/71))
- Support for typedefs. ([#74](https://github.com/fabianschuiki/moore/issues/74))
- Support for port assignments in instantiations. ([#77](https://github.com/fabianschuiki/moore/issues/77))
- Support for continuous assignments in modules.
- Support for bitwise logic operators.

### Fixed
- Fix assigning values to output ports.
- Fix semantics of `always_comb` blocks; they are now run once at startup and then implicitly when an input changes.

### Changed
- The first verbosity level (`-v`) does no longer print info lines.

### Fixed
- Fix code generated by `repeat` statement.

## 0.2.0 - 2019-01-24
### Added
- Support for if-generate and for-generate blocks. ([#72](https://github.com/fabianschuiki/moore/issues/72), [#73](https://github.com/fabianschuiki/moore/issues/73))
- Support for value and type parameters.
- Support for module instantiations and processes.
- Support for signal declarations.

### Changed
- Use [salsa](https://github.com/salsa-rs/salsa) to implement SystemVerilog queries.
- Add usage example to README, plus some cleanup.
- Switch to dual-licensing.
- Update llhd to v0.3.0.
- Improve command line help page.

## 0.1.0 - 2018-02-27
### Added
- Initial release
- Basic SystemVerilog and VHDL parsing
