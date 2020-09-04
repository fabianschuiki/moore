// RUN: moore %s -e foo -O0
module foo;
    type("foo") x0;
    type("hello") x1;
    var x2 = "world!";
    // CHECK: %x0 = sig i24 %0
    // CHECK: %x1 = sig i40 %1
    // CHECK: %x2 = sig i48 %2
endmodule
