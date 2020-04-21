module split_ports (a[7:4], a[3:0]);
    // First port is upper 4 bits of 'a'.
    // Second port is lower 4 bits of 'a'.
    // Cannot use named port connections because
    // of part-select port 'a'.
endmodule
