// RUN: moore %s -e a0 -Vtypes
module a0;
    logic [15:0] x, y;

    initial begin
        if (x);
        // CHECK: 6: cast_type(x) = logic
        // CHECK: 6: self_type(x) = logic [15:0]
        // CHECK: 6: type_context(x) = <bool>
        while (x);
        // CHECK: 10: cast_type(x) = logic
        // CHECK: 10: self_type(x) = logic [15:0]
        // CHECK: 10: type_context(x) = <bool>
        do begin
        end while (x);
        // CHECK: 15: cast_type(x) = logic
        // CHECK: 15: self_type(x) = logic [15:0]
        // CHECK: 15: type_context(x) = <bool>
    end
endmodule
