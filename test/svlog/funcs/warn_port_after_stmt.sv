// RUN: moore %s
// IGNORE  not yet triggered because func args canonicalization is lazy

function myfunc2;
    input int x;
    int y;
    input int z;
    // CHECK: warning: port after statement
endfunction
