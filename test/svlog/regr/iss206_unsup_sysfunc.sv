// RUN: moore %s -e foo
// FAIL

module foo;
    initial $bar();
    // CHECK-ERR: error: unknown system task `$bar`
endmodule
