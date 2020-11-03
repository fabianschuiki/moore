// RUN: moore %s

function myfunc2;
    input int x;
    int y;
    input int z;
    // CHECK: warning: port after statement
endfunction
