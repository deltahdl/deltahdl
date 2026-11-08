#include <gtest/gtest.h>

#include <cstdint>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(OperatorElaboration, UnaryReductionAndElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic x;\n"
      "  initial x = &a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, UnaryReductionNandElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic x;\n"
      "  initial x = ~&a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, UnaryReductionOrElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic x;\n"
      "  initial x = |a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, UnaryReductionNorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic x;\n"
      "  initial x = ~|a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, UnaryReductionXorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic x;\n"
      "  initial x = ^a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, UnaryReductionXnorElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic x;\n"
      "  initial x = ~^a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, UnaryReductionXnorAltElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic x;\n"
      "  initial x = ^~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, UnaryReductionOnRealOperandRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  logic x;\n"
      "  initial x = &r;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unary operator '&' is not allowed on real operands", 4, "11.3.1"));
}

TEST(AlwaysCombBasicSim, AlwaysCombReductionAnd) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic result;\n"
      "  initial a = 4'b1111;\n"
      "  always_comb begin\n"
      "    result = &a;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AlwaysCombExtendedSim, AlwaysCombReductionOr) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic y;\n"
      "  always_comb y = |a;\n"
      "  initial begin\n"
      "    a = 8'h01;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(OperatorElaboration, ReductionOperatorsFoldInConstantExpressions) {
  EvalFixture f;
  const struct {
    const char* text;
    int64_t value;
  } kWant[] = {{"&4'b0100", 0},  {"~&4'b0100", 1}, {"|4'b0100", 1},
               {"~|4'b0100", 0}, {"^4'b0100", 1},  {"~^4'b0100", 0},
               {"^~4'b0100", 0}, {"&4'b1111", 1},  {"|{8'h1, 64'h0}", 1}};
  for (const auto& want : kWant) {
    EXPECT_EQ(ConstEvalInt(ParseExprFrom(want.text, f)), want.value)
        << want.text;
  }
}

TEST(OperatorElaboration, ReductionInGenerateConditionSelectsTheBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter logic [3:0] M = 4'b0100);\n"
      "  if (|M) begin : g_on\n"
      "    logic x;\n"
      "  end else begin : g_off\n"
      "    logic y;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
