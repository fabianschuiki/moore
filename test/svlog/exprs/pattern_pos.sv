// RUN: moore %s -e foo -O0
module foo;
    struct {
        byte a;
        int b;
        struct packed {
            shortint x;
            longint y;
        } c;
    } p;
    int [3:0] q;

    initial begin
        p = '{1, 42, '{1337, 9001}};
        q = '{1, 2, 3, 4};
    end
endmodule
