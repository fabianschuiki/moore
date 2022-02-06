// RUN: moore -e foo --format=mlir-native %s | FileCheck %s

// CHECK-LABEL: func @ReturnStmt() -> i32 {
function int ReturnStmt;
    // CHECK-NEXT: [[TMP:%.+]] = hw.constant 42 : i32
    // CHECK-NEXT: return [[TMP]]
    return 42;
endfunction

// CHECK-LABEL: func @UnreachableReturns() -> i32 {
function int UnreachableReturns;
    // CHECK-NEXT:   [[TMP:%.+]] = hw.constant 42 : i32
    // CHECK-NEXT:   return [[TMP]]
    return 42;
    // CHECK-NEXT: ^[[BB:.+]]: // no predecessors
    // CHECK-NEXT:   [[TMP:%.+]] = hw.constant 9001 : i32
    // CHECK-NEXT:   return [[TMP]]
    return 9001;
endfunction

// CHECK-LABEL: func @BreakStmt() {
function void BreakStmt;
    // CHECK-NEXT: br ^[[LOOP:.+]]
    forever begin
        // CHECK-NEXT: ^[[LOOP]]:
        // CHECK-NEXT:   br ^[[EXIT:.+]]
        break;
    end
    // CHECK-NEXT: ^[[EXIT]]:
    // CHECK-NEXT:   return
endfunction

// CHECK-LABEL: func @BreakStmtWithUnreachableCode() {
function void BreakStmtWithUnreachableCode;
    // CHECK-NEXT: [[TMP:%.+]] = hw.constant
    // CHECK-NEXT: [[VAR:%.+]] = llhd.var [[TMP]]
    int x;
    // CHECK-NEXT: br ^[[LOOP:.+]]
    forever begin
        // CHECK-NEXT: ^[[LOOP]]:
        // CHECK-NEXT:   llhd.load [[VAR]]
        x;
        // CHECK-NEXT:   br ^[[EXIT:.+]]
        break;
        // CHECK-NEXT: ^{{.+}}: // no predecessors
        // CHECK-NEXT:   llhd.load [[VAR]]
        // CHECK-NEXT:   br ^[[LOOP]]
        x;
    end
    // CHECK-NEXT: ^[[EXIT]]:
    // CHECK-NEXT:   return
endfunction

// CHECK-LABEL: func @ContinueStmt() {
function void ContinueStmt;
    // CHECK-NEXT: br ^[[LOOP:.+]]
    forever begin
        // CHECK-NEXT: ^[[LOOP]]:
        // CHECK-NEXT:   br ^[[LOOP]]
        continue;
    end
    // CHECK-NEXT: ^[[EXIT:.+]]: // no predecessors
    // CHECK-NEXT:   return
endfunction

// CHECK-LABEL: func @ContinueStmtWithUnreachableCode() {
function void ContinueStmtWithUnreachableCode;
    // CHECK-NEXT: [[TMP:%.+]] = hw.constant
    // CHECK-NEXT: [[VAR:%.+]] = llhd.var [[TMP]]
    int x;
    // CHECK-NEXT: br ^[[LOOP:.+]]
    forever begin
        // CHECK-NEXT: ^[[LOOP]]:
        // CHECK-NEXT:   llhd.load [[VAR]]
        x;
        // CHECK-NEXT:   br ^[[LOOP]]
        continue;
        // CHECK-NEXT: ^{{.+}}: // no predecessors
        // CHECK-NEXT:   llhd.load [[VAR]]
        // CHECK-NEXT:   br ^[[LOOP]]
        x;
    end
    // CHECK-NEXT: ^[[EXIT:.+]]: // no predecessors
    // CHECK-NEXT:   return
endfunction

module foo;
endmodule
