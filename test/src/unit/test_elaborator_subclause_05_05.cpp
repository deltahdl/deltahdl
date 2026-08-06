#include "fixture_elaborator.h"

namespace {

TEST(OperatorElaboration, SingleCharOperatorElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a, b, c;\n"
             "  assign a = b + c;\n"
             "endmodule\n"));
}

TEST(OperatorElaboration, DoubleCharOperatorElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a, b;\n"
             "  assign a = b << 1;\n"
             "endmodule\n"));
}

TEST(OperatorElaboration, TripleCharOperatorElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a, b;\n"
             "  assign a = b <<< 1;\n"
             "endmodule\n"));
}

TEST(OperatorElaboration, UnaryOperatorElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a, b;\n"
             "  assign a = ~b;\n"
             "endmodule\n"));
}

TEST(OperatorElaboration, BinaryOperatorElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a, b, c;\n"
             "  assign a = b & c;\n"
             "endmodule\n"));
}

TEST(OperatorElaboration, ConditionalOperatorElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic sel;\n"
             "  logic [7:0] a, b, c;\n"
             "  assign a = sel ? b : c;\n"
             "endmodule\n"));
}

TEST(OperatorElaboration, MixedOperatorsElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a, b, c, d;\n"
             "  assign a = (b + c) & ~d;\n"
             "endmodule\n"));
}

TEST(OperatorElaboration, OperatorInContinuousAssignElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic a, b, c;\n"
             "  assign a = b | c;\n"
             "  assign b = ~c;\n"
             "endmodule\n"));
}

TEST(OperatorElaboration, OperatorInAlwaysBlockElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a, b, c;\n"
             "  always_comb begin\n"
             "    a = b + c;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(OperatorElaboration, CompoundAssignmentElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a;\n"
             "  initial begin\n"
             "    a = 8'd0;\n"
             "    a += 8'd1;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
