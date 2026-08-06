#include "fixture_elaborator.h"
#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(AssignmentPatternElaboration, ReplicationPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = '{4{8'hAB}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, IntegerAtomTypePatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = int'{42};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ConstantAssignmentPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int arr [3] = '{10, 20, 30};\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, TypeReferencePatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] x;\n"
      "  initial x = type(x)'{8'd1, 8'd2};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, LhsPositionalPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial '{a, b} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ErrorPatternExpressionInPort) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(input int a);\n"
      "endmodule\n"
      "module top;\n"
      "  sub u(.a(int'{42}));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ErrorLhsNamedKeys) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] x, y;\n"
      "  initial '{a: x, b: y} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ErrorNonConstantInConstantPattern) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  localparam int arr [3] = '{x, 2, 3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §10.9 footnote 37: the members of a constant assignment pattern shall be
// constant expressions. A named parameter is a constant expression (11.2.1) and
// resolves through a different const-eval path than a literal token, so the
// accepting path is exercised here with parameter members.
TEST(AssignmentPatternElaboration, ConstantPatternWithParameterMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = 10;\n"
      "  parameter int B = 20;\n"
      "  localparam int arr [2] = '{A, B};\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.9 footnote 37: a localparam is likewise a constant expression and is a
// distinct constant form from both a literal and a parameter; the accepting
// path is exercised here with localparam members.
TEST(AssignmentPatternElaboration, ConstantPatternWithLocalparamMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int A = 5;\n"
      "  localparam int arr [2] = '{A, A};\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ExpressionUsableOutsideAssignmentSide) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial x = int'{40} + 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ErrorTypedLhsPatternNamedKeys) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] x, y;\n"
      "  initial pair_t'{a: x, b: y} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ErrorLhsPatternBitCountMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial '{a, b} = 32'hDEADBEEF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
