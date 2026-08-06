#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(OperandElaboration, VariableReferenceElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] a, b;\n"
             "  initial a = b;\n"
             "endmodule\n"));
}

TEST(OperandElaboration, ParameterReferenceElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = 99;\n"
             "  int x;\n"
             "  initial x = P;\n"
             "endmodule\n"));
}

TEST(OperandElaboration, LocalparamReferenceElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  localparam int LP = 7;\n"
             "  int x;\n"
             "  initial x = LP;\n"
             "endmodule\n"));
}

TEST(OperandElaboration, ConcatenationOperandElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [3:0] a, b;\n"
             "  logic [7:0] c;\n"
             "  initial c = {a, b};\n"
             "endmodule\n"));
}

TEST(OperandElaboration, NestedConcatenationOperandElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [3:0] a, b, c;\n"
             "  logic [11:0] d;\n"
             "  initial d = {a, {b, c}};\n"
             "endmodule\n"));
}

TEST(OperandElaboration, FunctionCallOperandElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function automatic int foo();\n"
             "    return 1;\n"
             "  endfunction\n"
             "  int x;\n"
             "  initial x = foo();\n"
             "endmodule\n"));
}

TEST(OperandElaboration, UnpackedArrayElementOperandElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int arr[4];\n"
             "  int x;\n"
             "  initial x = arr[2];\n"
             "endmodule\n"));
}

TEST(OperandElaboration, BitSelectOperandElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] a;\n"
             "  logic b;\n"
             "  initial b = a[3];\n"
             "endmodule\n"));
}

TEST(OperandElaboration, PartSelectOperandElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] a;\n"
             "  logic [3:0] b;\n"
             "  initial b = a[3:0];\n"
             "endmodule\n"));
}

TEST(OperandElaboration, NetReferenceElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire [7:0] w;\n"
             "  logic [7:0] x;\n"
             "  assign w = 8'hA5;\n"
             "  initial x = w;\n"
             "endmodule\n"));
}

TEST(OperandElaboration, BitSelectOfNetElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  wire [7:0] w;\n"
             "  logic b;\n"
             "  assign w = 8'hA5;\n"
             "  initial b = w[3];\n"
             "endmodule\n"));
}

// §11.5 para 2 lists a packed structure among the base types that admit a
// bit-select operand. Elaboration must accept selecting a bit of a packed
// struct rather than rejecting it as a bit-select of a scalar: a packed
// aggregate is excluded from the scalar-select check, unlike a plain `logic b`.
TEST(OperandElaboration, PackedStructBitSelectOperandElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
             "  logic b;\n"
             "  initial b = s[3];\n"
             "endmodule\n"));
}

// §11.5 para 2 likewise lists a packed structure as a base type for a
// part-select operand.
TEST(OperandElaboration, PackedStructPartSelectOperandElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  struct packed { logic [3:0] hi; logic [3:0] lo; } s;\n"
             "  logic [3:0] b;\n"
             "  initial b = s[7:4];\n"
             "endmodule\n"));
}

// §11.5 para 2 lists a packed array among the base types that admit bit-select
// and part-select operands. A packed-array variable is registered on the
// packed-array path (not the scalar path), so selecting from it must elaborate;
// §7.4.1 supplies the multi-dimensional packed declaration.
TEST(OperandElaboration, PackedArraySelectOperandElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [1:0][7:0] arr;\n"
             "  logic b;\n"
             "  logic [3:0] nib;\n"
             "  initial begin b = arr[1][0]; nib = arr[1][7:4]; end\n"
             "endmodule\n"));
}

// §11.5 para 2 lists a parameter among the base types that admit bit-select and
// part-select operands (a parameter is a constant operand, §11.2.1). Both forms
// over a vector parameter must elaborate cleanly.
TEST(OperandElaboration, ParameterBitAndPartSelectOperandElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter [15:0] P = 16'hABCD;\n"
             "  logic b;\n"
             "  logic [7:0] hi;\n"
             "  initial begin b = P[0]; hi = P[15:8]; end\n"
             "endmodule\n"));
}

}  // namespace
