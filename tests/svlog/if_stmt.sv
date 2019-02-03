module A;
	int a;
	initial if (a == 42) a = 16; else a = 9001;
endmodule

//@ elab A
//| proc @n223 (i32$ %0) (i32$ %1) {
//| %2:
//|     %3 = prb %1
//|     %4 = cmp eq i32 %3 42
//|     br %4 label %if_true %if_false
//| %if_true:
//|     drv %1 16 1e
//|     wait %8 for 1e
//| %if_false:
//|     drv %1 9001 1e
//|     wait %11 for 1e
//| %if_exit:
//|     halt
//| %8:
//|     br label %if_exit
//| %11:
//|     br label %if_exit
//| }
//|
//| entity @A () () {
//|     %a = sig i32
//|     inst @n223 (%a) (%a)
//| }
