# Syntax

Depending on whether ANSI or non-ANSI headers are used, ports require different treatment during name resolution. The syntax is as follows:

    # nonansi_port
    expr
    "." ident "(" [expr] ")"

    # ansi_port
    [direction] [net_type|"var"] type_or_implicit ident {dimension} ["=" expr]
    "interface" ["." ident] ident {dimension} ["=" expr]
    [direction] "." ident "(" [expr] ")"

In the non-ANSI form, the port identifier is not declared. The expressions can only contain identifiers, simple concatenations `{a,b,c}`, indexations `a[i]`, and member accesses `a.d`. Each identifier in such an expression (not considering the index expression or member names) shall be bound to a declaration within the module.

In the ANSI form, the port identifier is declared. Furthermore, the names in the expression are bound regularly.

To simplify parsing, the above rules are generalized to the following grammar, the resulting AST of which shall be disassembled and checked for validity upon lowering to HIR:

    "interface" ["." ident] ident {dimension} ["=" expr]
    [direction] "." ident "(" [expr] ")"
    [direction] [net_type|"var"] type_or_implicit ident {dimension} ["=" expr]
    expr

A port consisting only of an identifier shall be treated as the third variant rather than the fourth. The variants are, in order: interface port, explicit port, named port, implicit port.


# HIR

Ports shall be split into three different structures:

1) A port list in which each port is either an identifier, concatenation of identifiers, or a part-select of an identifier.
2) Multiple port declarations which assign to each port a direction and a reference to a variable or net declaration. These are referenced in the port list.
3) For each port declaration one of the following:
    - variable declaration
    - net declaration
    - interface instantiation
    - modport instantiation
    - expression

Ports can have the following direction:

- input
- output
- inout
- ref
- interface
