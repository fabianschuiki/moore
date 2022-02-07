// RUN: moore -e foo --format=mlir-native %s | FileCheck %s

// CHECK-LABEL: func @VoidFunc() {
// CHECK-NEXT:    return
// CHECK-NEXT:  }
function void VoidFunc;
endfunction

// CHECK-LABEL: func @RetOnlyFunc() -> i32 {
// CHECK-NEXT:    [[TMP:%.+]] = hw.constant 42 :
// CHECK-NEXT:    return [[TMP]]
// CHECK-NEXT:  }
function int RetOnlyFunc;
    return 42;
endfunction

// CHECK-LABEL: func @InputArgs(
// CHECK-SAME:    [[X:%.+]]: i32, [[Y:%.+]]: i32
// CHECK-SAME:  ) -> i32 {
// CHECK-NEXT:    [[TMP:%.+]] = comb.add [[X]], [[Y]]
// CHECK-NEXT:    return [[TMP]]
// CHECK-NEXT:  }
function int InputArgs(int x, int y);
    return x + y;
endfunction

// CHECK-LABEL: func @OutputArgs(
// CHECK-SAME:    [[X:%.+]]: !llhd.ptr<i32>, [[Y:%.+]]: !llhd.ptr<i32>
// CHECK-SAME:  ) {
// CHECK-NEXT:    [[TMP:%.+]] = hw.constant 0 :
// CHECK-NEXT:    llhd.store [[X]], [[TMP]] :
// CHECK-NEXT:    [[TMP:%.+]] = hw.constant 42 :
// CHECK-NEXT:    llhd.store [[Y]], [[TMP]] :
// CHECK-NEXT:    [[TMP:%.+]] = hw.constant 9001 :
// CHECK-NEXT:    llhd.store [[X]], [[TMP]] :
// CHECK-NEXT:    return
// CHECK-NEXT:  }
function void OutputArgs(output int x, int y = 42);
    x = 9001;
endfunction

// CHECK-LABEL: func @InoutArgs(
// CHECK-SAME:    [[X:%.+]]: !llhd.ptr<i32>, [[Y:%.+]]: !llhd.ptr<i32>
// CHECK-SAME:  ) {
// CHECK-NEXT:    [[TMP1:%.+]] = llhd.load [[X]] :
// CHECK-NEXT:    [[TMP2:%.+]] = llhd.load [[Y]] :
// CHECK-NEXT:    [[TMP3:%.+]] = comb.mul [[TMP1]], [[TMP2]]
// CHECK-NEXT:    llhd.store [[X]], [[TMP3]] :
// CHECK-NEXT:    return
// CHECK-NEXT:  }
function void InoutArgs(inout int x, inout int y = 42);
    x *= y;
endfunction

// CHECK-LABEL: func @RefArgs(
// CHECK-SAME:    [[X:%.+]]: !llhd.ptr<i32>, [[Y:%.+]]: !llhd.ptr<i32>
// CHECK-SAME:  ) -> i32 {
// CHECK-NEXT:    [[TMP1:%.+]] = llhd.load [[X]] :
// CHECK-NEXT:    [[TMP2:%.+]] = llhd.load [[Y]] :
// CHECK-NEXT:    [[TMP3:%.+]] = comb.mul [[TMP1]], [[TMP2]]
// CHECK-NEXT:    return [[TMP3]] :
// CHECK-NEXT:  }
function int RefArgs(ref int x, const ref int y);
    return x * y;
endfunction

// CHECK-LABEL: func @Calls() {
function void Calls;
    // CHECK: [[A:%.+]] = llhd.var
    // CHECK: [[B:%.+]] = llhd.var
    int a, b;
    // CHECK-NEXT: call @VoidFunc()
    VoidFunc();

    // CHECK-NEXT: [[TMP:%.+]] = call @RetOnlyFunc()
    // CHECK-NEXT: llhd.store [[A]], [[TMP]]
    a = RetOnlyFunc();

    // CHECK-NEXT: [[TMP1:%.+]] = llhd.load [[A]]
    // CHECK-NEXT: [[TMP2:%.+]] = llhd.load [[A]]
    // CHECK-NEXT: [[TMP:%.+]] = call @InputArgs([[TMP1]], [[TMP2]])
    // CHECK-NEXT: llhd.store [[A]], [[TMP]]
    a = InputArgs(a, a);

    // CHECK: [[TMP_A:%.+]] = llhd.var
    // CHECK: [[TMP_B:%.+]] = llhd.var
    // CHECK-NEXT: call @OutputArgs([[TMP_A]], [[TMP_B]])
    // CHECK-NEXT: [[TMP:%.+]] = llhd.load [[TMP_A]]
    // CHECK-NEXT: llhd.store [[A]], [[TMP]]
    // CHECK-NEXT: [[TMP:%.+]] = llhd.load [[TMP_B]]
    // CHECK-NEXT: llhd.store [[B]], [[TMP]]
    OutputArgs(a, b);
    // CHECK: [[TMP_A:%.+]] = llhd.var
    // CHECK: [[TMP_B:%.+]] = llhd.var
    // CHECK-NEXT: call @OutputArgs([[TMP_A]], [[TMP_B]])
    // CHECK-NEXT: [[TMP:%.+]] = llhd.load [[TMP_A]]
    // CHECK-NEXT: llhd.store [[A]], [[TMP]]
    OutputArgs(a,);

    // CHECK-NEXT: [[TMP:%.+]] = llhd.load [[A]]
    // CHECK-NEXT: [[TMP_A:%.+]] = llhd.var [[TMP]]
    // CHECK-NEXT: [[TMP:%.+]] = llhd.load [[B]]
    // CHECK-NEXT: [[TMP_B:%.+]] = llhd.var [[TMP]]
    // CHECK-NEXT: call @InoutArgs([[TMP_A]], [[TMP_B]])
    // CHECK-NEXT: [[TMP:%.+]] = llhd.load [[TMP_A]]
    // CHECK-NEXT: llhd.store [[A]], [[TMP]]
    // CHECK-NEXT: [[TMP:%.+]] = llhd.load [[TMP_B]]
    // CHECK-NEXT: llhd.store [[B]], [[TMP]]
    InoutArgs(a, b);
    // CHECK-NEXT: [[TMP:%.+]] = llhd.load [[A]]
    // CHECK-NEXT: [[TMP_A:%.+]] = llhd.var [[TMP]]
    // CHECK-NEXT: [[TMP:%.+]] = hw.constant 42 :
    // CHECK-NEXT: [[TMP_B:%.+]] = llhd.var [[TMP]]
    // CHECK-NEXT: call @InoutArgs([[TMP_A]], [[TMP_B]])
    // CHECK-NEXT: [[TMP:%.+]] = llhd.load [[TMP_A]]
    // CHECK-NEXT: llhd.store [[A]], [[TMP]]
    InoutArgs(a,);

    // CHECK-NEXT: call @RefArgs([[A]], [[B]])
    RefArgs(a, b);

    // CHECK-NEXT: return
endfunction

module foo;
endmodule
