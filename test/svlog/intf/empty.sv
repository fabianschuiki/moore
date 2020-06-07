// RUN: moore %s -e foo

module foo;
	bar x();
endmodule

interface bar;
endinterface

// CHECK: entity @foo () -> () {
// CHECK: }
