// RUN: moore %s -e top
// IGNORE

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
