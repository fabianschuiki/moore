// RUN: moore %s -e foo
// Default values for positional arguments from IEEE 1800-2017 section 13.5.3
// IGNORE  part of #213

function bar(int j = 0, int k, int data = 1);
endfunction

module foo;
    initial begin
        bar(,5);    // is equivalent to bar(0, 5, 1);
        bar(2,5);   // is equivalent to bar(2, 5, 1);
        bar(,5,);   // is equivalent to bar(0, 5, 1);
        bar(,5,7);  // is equivalent to bar(0, 5, 7);
        bar(1,5,2); // is equivalent to bar(1, 5, 2);
        bar();      // error; k has no default value
        bar(1,,7);  // error; k has no default value
    end
endmodule
