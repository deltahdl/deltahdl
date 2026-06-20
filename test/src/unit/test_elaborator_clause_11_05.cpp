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

}  // namespace
