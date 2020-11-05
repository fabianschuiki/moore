// RUN: moore %s -e foo -Vcall-args
// FAIL

function bar(int j = 0, int k, int data = 1);
endfunction

module foo;
    initial begin
        bar(1,,7);  // error; k has no default value
        // CHECK-ERR: error: argument without default: `k` must be passed a value
    end
endmodule
