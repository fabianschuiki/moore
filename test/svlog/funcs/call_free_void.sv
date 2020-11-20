// RUN: moore %s -e foo

function void bar;
endfunction

module foo;
    initial bar();
endmodule

// CHECK:      func %bar () void {
// CHECK-NEXT: 0:
// CHECK-NEXT:     ret
// CHECK-NEXT: }
