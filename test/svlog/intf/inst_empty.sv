// RUN: moore %s -e foo -O0

module foo;
	bar x();
endmodule

interface bar;
endinterface

// CHECK: entity @foo () -> () {
// CHECK: }
