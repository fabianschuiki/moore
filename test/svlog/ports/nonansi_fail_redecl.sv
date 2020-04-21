// RUN: moore %s -e foo
// FAIL
module foo(a, b, c, d);
    input a;
    output a;
    // CHECK: error: port `a` declared multiple times

    input b;
    logic b;
    logic b;
    // CHECK: error: port variable `b` declared multiple times

    input c;
    wire c;
    wire c;
    // CHECK: error: port net `c` declared multiple times

    input d;
    wire d;
    logic d;
    // CHECK: error: port `d` doubly declared as variable and net
endmodule
