module A;
	bit a, b, c, d;
	always_ff @(a, posedge b or negedge c iff d);
endmodule

//@ elab A
//| proc @n227 (i1$ %0, i1$ %1, i1$ %2, i1$ %3) () {
//| %4:
//|     br label %init
//| %init:
//|     %a = prb %0
//|     %b = prb %1
//|     %c = prb %2
//|     wait %check, %0, %1, %2
//| %check:
//|     %a0 = prb %0
//|     %impledge = cmp neq i1 %a %a0
//|     %b0 = prb %1
//|     %7 = cmp eq i1 %b 0
//|     %8 = cmp neq i1 %b0 0
//|     %posedge = and i1 %7 %8
//|     %event_or = or i1 %impledge %posedge
//|     %c0 = prb %2
//|     %9 = cmp eq i1 %c0 0
//|     %10 = cmp neq i1 %c 0
//|     %negedge = and i1 %9 %10
//|     %d = prb %3
//|     %iff = and i1 %negedge %d
//|     %event_or0 = or i1 %event_or %iff
//|     br %event_or0 label %event %init
//| %event:
//|     br label %4
//| }
//|
//| entity @A () () {
//|     %a = sig i1
//|     %b = sig i1
//|     %c = sig i1
//|     %d = sig i1
//|     inst @n227 (%a, %b, %c, %d) ()
//| }

module B;
	bit clk;
	int count;

	always_ff @(posedge clk) begin
		count = 1;
	end

	initial begin
		#1ns clk = 1;
		#1ns clk = 0;
		#1ns;
	end
endmodule
