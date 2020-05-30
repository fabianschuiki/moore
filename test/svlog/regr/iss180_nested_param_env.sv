// RUN: moore %s -e foo

module foo;
    alice #(.T(int)) u0(.x(42));
endmodule

module alice #(parameter type T)(input T x);
    bob u1(.y(x));
endmodule

module bob (input int y);
endmodule
