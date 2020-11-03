// RUN: moore %s

function foo(
    input logic a,
    output logic b,
    inout logic c,
    ref logic d,
    const ref logic e
);
endfunction
