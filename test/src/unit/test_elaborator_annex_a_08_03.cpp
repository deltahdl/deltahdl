#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ExpressionElaboration, ConstantExpressionInParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 2 + 3;\n"
      "  logic [P-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConstantTernaryInParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter A = 1;\n"
      "  parameter B = (A > 0) ? 8 : 16;\n"
      "  logic [B-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConstantExpressionInLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter W = 4;\n"
      "  localparam MASK = (1 << W) - 1;\n"
      "  logic [W-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, GenvarExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConditionalExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, x;\n"
      "  assign x = a ? b : 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, InsideExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic hit;\n"
      "  initial hit = x inside {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, IncDecExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    i++;\n"
      "    ++i;\n"
      "    i--;\n"
      "    --i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, PartSelectAndIndexedRangeElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] a, b, c;\n"
      "  assign a = data[15:8];\n"
      "  assign b = data[0+:8];\n"
      "  assign c = data[15-:8];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, MintypMaxExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (1:2:3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ConstantParamExpressionDollarElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, TaggedUnionExpressionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { int v; void i; } u_t;\n"
      "  u_t u;\n"
      "  initial u = tagged v 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ParamExpressionDataTypeOverrideElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub #(parameter type T = int);\n"
      "  T data;\n"
      "endmodule\n"
      "module m;\n"
      "  sub #(.T(logic [7:0])) inst();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ExpressionElaboration, ExprOperatorAssignmentElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer x, y;\n"
      "  initial begin\n"
      "    y = 1;\n"
      "    x = (y += 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
