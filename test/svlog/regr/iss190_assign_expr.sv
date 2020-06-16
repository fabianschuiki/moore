// RUN: moore %s -e foo -O0

module foo;
    int i, j;
    initial begin
        i = (j = 1);
        i = (j += 1);
        i = (j -= 1);
        i = (j *= 1);
        i = (j /= 1);
        i = (j %= 1);
        i = (j &= 1);
        i = (j |= 1);
        i = (j ^= 1);
        i = (j <<= 1);
        i = (j >>= 1);
        i = (j <<<= 1);
        i = (j >>>= 1);
    end
endmodule
