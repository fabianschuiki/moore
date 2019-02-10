module A #(int K = 42);
	localparam L = 9001;

	initial begin
		int v = K;
		v = 0 + K;
		int w = L;
		w = 0 + L;
	end

	for (genvar i = 0; i < 2; i++) begin
		initial begin
			int v = i;
			v = 0 + i;
		end
	end
endmodule

//@ elab A
//| proc @A.initial.228.0 () () {
//| %0:
//|     %v = var i32
//|     store i32 %v 0
//|     %2 = add i32 0 0
//|     store i32 %v %2
//|     halt
//| }
//|
//| proc @A.initial.228.1 () () {
//| %0:
//|     %v = var i32
//|     store i32 %v 1
//|     %2 = add i32 0 1
//|     store i32 %v %2
//|     halt
//| }
//|
//| proc @A.initial.223.0 () () {
//| %0:
//|     %v = var i32
//|     store i32 %v 42
//|     %2 = add i32 0 42
//|     store i32 %v %2
//|     %w = var i32
//|     store i32 %w 9001
//|     %5 = add i32 0 9001
//|     store i32 %w %5
//|     halt
//| }
//|
//| entity @A () () {
//|     inst @A.initial.228.0 () ()
//|     inst @A.initial.228.1 () ()
//|     inst @A.initial.223.0 () ()
//| }
