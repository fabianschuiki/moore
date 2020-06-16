// RUN: moore %s -e foo

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
