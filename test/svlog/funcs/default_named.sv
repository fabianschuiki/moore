// RUN: moore %s -e foo
// Default values for named arguments from IEEE 1800-2017 section 13.5.4

function bar(int j = 1, int s = 0);
endfunction

module foo;
    initial begin
        bar(.j(2),.s(1)); // is equivalent to bar(2, 1);
        bar(.s(1));       // is equivalent to bar(1, 1);
        bar(,1);          // is equivalent to bar(1, 1);
        bar(.j(2));       // is equivalent to bar(2, 0);
        bar(.s(1),.j(2)); // is equivalent to bar(2, 1);
        bar(.s(),.j());   // is equivalent to bar(1, 0);
        bar(2);           // is equivalent to bar(2, 0);
        bar();            // is equivalent to bar(1, 0);
    end
endmodule
