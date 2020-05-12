// RUN: moore %s -e a0 -e a1 -e a2 -e a3 -Vtypes
module a0;
    logic [3:0] a;
    logic [8:0] b;
    // CHECK: 3: type(a) = logic [3:0]
    // CHECK: 4: type(b) = logic [8:0]

    assign a = (b + '1);
    // CHECK: 8: cast_type(a) = logic [3:0]
    // CHECK: 8: self_type(a) = logic [3:0]
    // CHECK: 8: type_context(a) = logic [8:0]

    // CHECK: 8: cast_type(b + '1) = logic [3:0]
    // CHECK: 8: self_type(b + '1) = logic [8:0]
    // CHECK: 8: operation_type(b + '1) = logic [8:0]
    // CHECK: 8: type_context(b + '1) = logic [3:0]

    // CHECK: 8: cast_type(b) = logic [8:0]
    // CHECK: 8: self_type(b) = logic [8:0]
    // CHECK: 8: type_context(b) = logic [8:0]

    // CHECK: 8: cast_type('1) = logic [8:0]
    // CHECK: 8: self_type('1) = logic
    // CHECK: 8: type_context('1) = logic [8:0]
endmodule

module a1;
    logic [14:0] a;
    logic [15:0] b;
    logic [15:0] sumA;
    logic [16:0] sumB;
    // CHECK: 28: type(a) = logic [14:0]
    // CHECK: 29: type(b) = logic [15:0]
    // CHECK: 30: type(sumA) = logic [15:0]
    // CHECK: 31: type(sumB) = logic [16:0]

    assign sumA = a + b;
    // CHECK: 37: cast_type(a + b) = logic [15:0]
    // CHECK: 37: self_type(a + b) = logic [15:0]
    // CHECK: 37: operation_type(a + b) = logic [15:0]
    // CHECK: 37: type_context(a + b) = logic [15:0]

    // CHECK: 37: cast_type(a) = logic [15:0]
    // CHECK: 37: self_type(a) = logic [14:0]
    // CHECK: 37: type_context(a) = logic [15:0]

    // CHECK: 37: cast_type(b) = logic [15:0]
    // CHECK: 37: self_type(b) = logic [15:0]
    // CHECK: 37: type_context(b) = logic [15:0]

    assign sumB = a + b;
    assign sumB = {a + b};
endmodule

module a2;
  logic [31:0] inst_data_i;
  logic [31:0] iimm;
  assign iimm = $signed({inst_data_i[31:20]});
endmodule

module a3;
    typedef struct packed {
        logic a;
        logic [3:0] b;
        logic [2:0] c;
    } str_t;
    str_t [0:0] x;

    initial x = '1;
endmodule

module foo #(parameter logic [7:0] N = 32'd19)(input logic [7:0] A = 32'd19);
endmodule

// This is broken for some reason.
module a4;
    parameter logic [7:0] x = 32'd42;
    localparam logic [7:0] y = 32'd42;
    logic [7:0] z = 32'd42;
    logic [7:0] w;

    initial begin
        logic [7:0] a = 32'd42;
        w = x;
        w = y;
        w = z;
        w = a;
    end

    foo #(.N(32'd42)) i_foo (.A(32'd42));
endmodule
