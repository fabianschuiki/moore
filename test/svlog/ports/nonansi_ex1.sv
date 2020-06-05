// RUN: moore %s -e test -Vports

module test(a,b,c,d,e,f,g,h);
    input [7:0] a;         // no explicit net declaration - net is unsigned
    input [7:0] b;
    input signed [7:0] c;
    input signed [7:0] d;  // no explicit net declaration - net is signed
    output [7:0] e;        // no explicit net declaration - net is unsigned
    output [7:0] f;
    output signed [7:0] g;
    output signed [7:0] h; // no explicit net declaration - net is signed

    wire signed [7:0] b;   // port b inherits signed attribute from net decl.
    wire [7:0] c;          // net c inherits signed attribute from port
    logic signed [7:0] f;  // port f inherits signed attribute from logic decl.
    logic [7:0] g;         // logic g inherits signed attribute from port

    // CHECK: Ports of `test`:
    // CHECK:   internal:
    // CHECK:     0: input wire logic [7:0] a
    // CHECK:     1: input wire logic signed [7:0] b
    // CHECK:     2: input wire logic signed [7:0] c
    // CHECK:     3: input wire logic signed [7:0] d
    // CHECK:     4: output wire logic [7:0] e
    // CHECK:     5: output var logic signed [7:0] f
    // CHECK:     6: output var logic signed [7:0] g
    // CHECK:     7: output wire logic signed [7:0] h
    // CHECK:   external:
    // CHECK:     0: .a(a)
    // CHECK:     1: .b(b)
    // CHECK:     2: .c(c)
    // CHECK:     3: .d(d)
    // CHECK:     4: .e(e)
    // CHECK:     5: .f(f)
    // CHECK:     6: .g(g)
    // CHECK:     7: .h(h)

    // CHECK: entity @test (i8$ %a, i8$ %b, i8$ %c, i8$ %d) -> (i8$ %e, i8$ %f, i8$ %g, i8$ %h) {
endmodule
