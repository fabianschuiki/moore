module complex_ports ({c,d}, .e(f));
    // Nets {c,d} receive the first port bits.
    // Name 'f' is declared inside the module.
    // Name 'e' is defined outside the module.
    // Cannot use named port connections of first port.
endmodule
