module a0;
	logic [3:0] a;
	logic [8:0] b;

	assign a = (b + '1);
endmodule

module a1;
	logic [14:0] a;
	logic [15:0] b;
	logic [15:0] sumA;
	logic [16:0] sumB;

	assign sumA = a + b;
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
