// RUN: moore %s -e foo1 -e foo2 -e foo3
// IGNORE  see issue #137

package magic;
endpackage

module foo1 import magic::*;;
endmodule

module foo2 import magic::*; ();
endmodule

module foo3 import magic::*; #() ();
endmodule
