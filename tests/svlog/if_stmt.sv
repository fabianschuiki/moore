module A;
	int a;
	initial if (a == 42) a = 16; else a = 9001;
endmodule

//@ elab A
//| proc @n223 (i32$ %0) (i32$ %1) {
//| %2:
//|     %a = prb %1
//|     %3 = cmp eq i32 %a 42
//|     br %3 label %if_true %if_false
//| %if_true:
//|     drv %1 16 0s 1e
//|     wait %7 for 0s 1e
//| %if_false:
//|     drv %1 9001 0s 1e
//|     wait %10 for 0s 1e
//| %if_exit:
//|     halt
//| %7:
//|     br label %if_exit
//| %10:
//|     br label %if_exit
//| }
//|
//| entity @A () () {
//|     %a = sig i32
//|     inst @n223 (%a) (%a)
//| }
