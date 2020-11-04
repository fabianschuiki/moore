// RUN: moore %s
// Function declaration examples from IEEE 1800-2017 section 13.4

function logic [15:0] myfunc1(int x, int y);
endfunction

function logic [15:0] myfunc2;
    input int x;
    input int y;
endfunction

function logic [15:0] myfunc3(int a, int b, output logic [15:0] u, v);
endfunction

function [3:0][7:0] myfunc4(input [3:0][7:0] a, b[3:0]);
endfunction
