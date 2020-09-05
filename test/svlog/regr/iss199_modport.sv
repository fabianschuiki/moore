// RUN: moore %s -e top

interface bus;
    logic clk;
    logic data;

    modport recv (
       input clk,
       input data
    );
endinterface

module testcase (
    bus.recv the_bus,
    output logic result
);
    always_ff @(posedge the_bus.clk) result <= the_bus.data;
endmodule

module top;
    bus bus_inst0(), bus_inst1();
    testcase test_inst0 (.the_bus(bus_inst0)); // this works
    testcase test_inst1 (.the_bus(bus_inst1.recv)); // this breaks
endmodule

// CHECK: entity @top () -> () {
// CHECK:     %bus_inst0.clk = sig i1 %0
// CHECK:     %bus_inst0.data = sig i1 %0
// CHECK:     %bus_inst1.clk = sig i1 %0
// CHECK:     %bus_inst1.data = sig i1 %0
// CHECK:     inst @testcase.param3 (i1$ %bus_inst0.clk, i1$ %bus_inst0.data) -> (i1$ %test_inst0.result.default)
// CHECK:     inst @testcase.param4 (i1$ %bus_inst1.clk, i1$ %bus_inst1.data) -> (i1$ %test_inst1.result.default)
// CHECK: }
