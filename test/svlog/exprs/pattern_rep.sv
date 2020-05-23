// RUN: moore %s -e foo -O0
module foo;
    int [1:2][1:3] n1 = '{'{0,1,2},'{3{4}}};
    int [1:2][1:6] n2 = '{2{'{3{4, 5}}}};
endmodule
