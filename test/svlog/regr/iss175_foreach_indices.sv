// RUN: moore %s
// Foreach loop indices should emit a definition.

module foo;
    int x;
    int [7:0] a;
    int [7:0][2:0] b;
    int [7:0][2:0][4:0] c;

    initial begin
        foreach (a[i]) x = i + a[i];
        foreach (b[i, j]) x = i + j + b[i][j];
        foreach (c[i, j, k]) x = i + j + k + c[i][j][k];
        foreach (c[i,  , k]) x = i +     k + c[i][1][k];
        foreach (c[ , j, k]) x =     j + k + c[1][j][k];
        foreach (c[ ,  , k]) x =         k + c[1][1][k];
    end
endmodule
