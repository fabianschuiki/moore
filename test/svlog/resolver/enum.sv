// RUN: moore %s -e A
module A;
    enum {
        Foo, Bar, Gax, Bux, Bla
    } c0;

    enum logic [41:0] {
        Baz, Buz
    } c1;

    initial begin
    	c0 = Foo;
    	c0 = Bar;
    	c1 = Baz;
    	c1 = Buz;
    end
endmodule
