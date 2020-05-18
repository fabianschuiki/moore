// RUN: moore %s -e foo -Vtypes

module foo;
    initial begin
        logic [7:0] regA, regB;
        logic signed [7:0] regS;

        regA = $unsigned(-4);     // regA = 8'b11111100
        regB = $unsigned(-4'sd4); // regB = 8'b00001100
        regS = $signed(4'b1100);  // regS = -4

        regA = unsigned'(-4);     // regS = -4
        regA = unsigned'(-4'sd4); // regS = -4
        regS = signed'(4'b1100);  // regA = 8'b11111100

        regS = regA + regB;                   // will do unsigned addition
        regS = byte'(regA) + byte'(regB);     // will do signed addition
        regS = signed'(regA) + signed'(regB); // will do signed addition
        regS = $signed(regA) + $signed(regB); // will do signed addition
    end
endmodule
