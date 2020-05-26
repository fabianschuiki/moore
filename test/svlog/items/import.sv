// RUN: moore %s -e foo -O0
// This also acts as a regression test for #100.

import pkgA::*;

module foo
    import pkgB::*;
();
    import pkgC::*;
    import pkgD::D;

    int a = A;
    int b = B;
    int c = C;
    int d = D;
endmodule

package pkgA; localparam int A = 1; endpackage
package pkgB; localparam int B = 42; endpackage
package pkgC; localparam int C = 1337; endpackage
package pkgD; localparam int D = 9001; endpackage
