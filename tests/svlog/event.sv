module A;
	bit a, b, c, d;
	always_ff @(a, posedge b or negedge c iff d);
endmodule

//@ elab A
//| proc @n226 (i1$ %0, i1$ %1, i1$ %2, i1$ %3) () {
//| %4:
//|     br label %init
//| %init:
//|     %6 = prb %0
//|     %7 = prb %1
//|     %8 = prb %2
//|     wait %check, %0, %1, %2
//| %check:
//|     %10 = prb %0
//|     %impledge = cmp neq i1 %6 %10
//|     %11 = prb %1
//|     %12 = cmp eq i1 %7 0
//|     %13 = cmp neq i1 %11 0
//|     %posedge = and i1 %12 %13
//|     %event_or = or i1 %impledge %posedge
//|     %14 = prb %2
//|     %15 = cmp eq i1 %14 0
//|     %16 = cmp neq i1 %8 0
//|     %negedge = and i1 %15 %16
//|     %17 = prb %3
//|     %iff = and i1 %negedge %17
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
//|     inst @n226 (%a, %b, %c, %d) ()
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

//@ elab B
