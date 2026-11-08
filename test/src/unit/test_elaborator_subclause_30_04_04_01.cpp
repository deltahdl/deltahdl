#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(OperatorElaboration, ModulePathOperandClassesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    specparam SP = 1;\n"
      "    if (a && en && SP) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, LocalVariableOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  logic gate;\n"
      "  specify\n"
      "    if (gate) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, PartSelectOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (a[1:0]) (a[0] => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, InoutPortOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, inout b, output y);\n"
      "  specify\n"
      "    if (b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BitSelectAndConstantOperandsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (a[0] && 1'b1) (a[0] => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, TableOperatorsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] a, input sel, output y);\n"
      "  specify\n"
      "    if (sel ? (~&a) : (^a | &a)) (a[0] => y) = 4;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BitwiseNegationOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (~a) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, LogicalNotOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (!a) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, LogicalEqualityOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a == b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, LogicalInequalityOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a != b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, LogicalOrOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a || b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BitwiseXnorOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ^~ b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BitwiseXnorAltOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ~^ b) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ReductionNorOperatorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (~|a) (a[0] => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ConcatenationOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if ({a, b}) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ReplicationOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if ({2{a}}) (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, OutputPortOperandIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (y) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operand 'y' may not be an output port", 3,
                            "30.4.4.1"));
}

TEST(OperatorElaboration, OutputPortBitSelectOperandIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [3:0] a, output [3:0] y);\n"
      "  specify\n"
      "    if (y[0]) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operand 'y' may not be an output port", 3,
                            "30.4.4.1"));
}

TEST(OperatorElaboration, ArithmeticOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (a + en) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '+' is not permitted in a state-dependent path "
      "conditional expression",
      4, "30.4.4.1"));
}

TEST(OperatorElaboration, RelationalOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (a > en) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '>' is not permitted in a state-dependent path "
      "conditional expression",
      4, "30.4.4.1"));
}

TEST(OperatorElaboration, ShiftOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (a << 1) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '<<' is not permitted in a state-dependent path "
      "conditional expression",
      3, "30.4.4.1"));
}

TEST(OperatorElaboration, CaseEqualityOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (a === en) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '===' is not permitted in a state-dependent path "
      "conditional expression",
      4, "30.4.4.1"));
}

TEST(OperatorElaboration, PowerOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a ** b) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '**' is not permitted in a state-dependent path "
      "conditional expression",
      3, "30.4.4.1"));
}

TEST(OperatorElaboration, UnaryArithmeticOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  specify\n"
      "    if (+a) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '+' is not permitted in a state-dependent path "
      "conditional expression",
      3, "30.4.4.1"));
}

TEST(OperatorElaboration, NestedDisallowedOperatorIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output y);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (en || (a - en)) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "binary operator '-' is not permitted in a state-dependent path "
      "conditional expression",
      4, "30.4.4.1"));
}

TEST(OperatorElaboration, PermittedOperatorStillAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output y);\n"
      "  specify\n"
      "    if (a & b) (a => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, ConditionOnEdgeSensitivePathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input a, output q);\n"
      "  wire en;\n"
      "  specify\n"
      "    if (en) (posedge clk => q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, OutputOperandOnEdgeSensitivePathIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input clk, input a, output q);\n"
      "  specify\n"
      "    if (q) (posedge clk => q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operand 'q' may not be an output port", 3,
                            "30.4.4.1"));
}

TEST(OperatorElaboration, HierarchicalNameOperandIsRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module mybuf(input a, output y);\n"
      "  assign y = a;\n"
      "  specify\n"
      "    if (top.b) (a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b; wire ty;\n"
      "  mybuf u(.a(a), .y(ty));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operand 'top.b' may not be a hierarchical name "
                            "reaching another scope",
                            4, "30.4.4.1"));
}

TEST(OperatorElaboration, InterfacePortMemberOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic a, en;\n"
      "endinterface\n"
      "module mybuf(ifc p, output y);\n"
      "  assign y = p.a;\n"
      "  specify\n"
      "    if (p.en) (p.a => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, InsideExpressionIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [1:0] a, input b, output y);\n"
      "  specify\n"
      "    if (a inside {1, 2}) (b => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an inside expression is not permitted in a "
                            "state-dependent path conditional expression",
                            3, "30.4.4.1"));
}

TEST(OperatorElaboration, CastIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [1:0] a, input b, output y);\n"
      "  specify\n"
      "    if (int'(a)) (b => y) = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a cast is not permitted in a state-dependent "
                            "path conditional expression",
                            3, "30.4.4.1"));
}

TEST(OperatorElaboration, StreamingConcatenationIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [1:0] a, input b, output y);\n"
      "  specify\n"
      "    if ({>>{a}}) (b => y) = 3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a streaming concatenation is not permitted in a "
                            "state-dependent path conditional expression",
                            3, "30.4.4.1"));
}

TEST(OperatorElaboration, AssignmentPatternIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input [1:0] a, input b, output y);\n"
      "  specify\n"
      "    if ('{a[0], b} == 2'b11) (b => y) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern is not permitted in a "
                            "state-dependent path conditional expression",
                            3, "30.4.4.1"));
}

TEST(OperatorElaboration, FunctionCallOperandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [1:0] a, input b, output y);\n"
      "  function automatic logic odd(logic [1:0] v);\n"
      "    return v[0];\n"
      "  endfunction\n"
      "  specify\n"
      "    if (odd(a)) (b => y) = 4;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
