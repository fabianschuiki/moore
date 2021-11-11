// RUN: moore %s -e foo

module foo;
    initial $bar();
    // CHECK-ERR: warning: unsupported: system task `$bar`; ignored
endmodule
