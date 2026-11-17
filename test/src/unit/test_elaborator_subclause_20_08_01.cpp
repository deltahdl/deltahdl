#include <gtest/gtest.h>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_param_value.h"

using namespace delta;

namespace {

TEST(ConstEval, Clog2) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(256)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(1)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(0)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(5)", f)), 3);
}

TEST(ConstEval, Clog2VectorArgument) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(16'd300)", f)), 9);
}

TEST(ConstEval, Clog2WideVectorArgument) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(40'd8589934593)", f)), 34);
}

TEST(ConstEval, Clog2TreatsArgumentAsUnsigned) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(-1)", f)), 64);
}

TEST(SubroutineCallExprElaboration, SystemTfCallAsExprElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = $clog2(256);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstExprElab, Clog2OfParameterArgumentFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int DEPTH = 300;\n"
      "  localparam int AW = $clog2(DEPTH);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  bool found = false;
  for (auto& p : design->top_modules[0]->params) {
    if (p.name == "AW") {
      found = true;
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 9);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ConstExprElab, Clog2OfPortParameterArgumentFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int DEPTH = 300);\n"
      "  localparam int AW = $clog2(DEPTH);\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  bool found = false;
  for (auto& p : design->top_modules[0]->params) {
    if (p.name == "AW") {
      found = true;
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 9);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ConstExprElab, DISABLED_Clog2FoldsANegativeArgumentAtItsOwnWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam byte B = -2;\n"
      "  localparam int A = $clog2(-1);\n"
      "  localparam int C = $clog2(-2);\n"
      "  localparam int D = $clog2(-8'sd1);\n"
      "  localparam int E = $clog2(B);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "A"), 32);
  EXPECT_EQ(ParamValue(design, "C"), 32);
  EXPECT_EQ(ParamValue(design, "D"), 8);
  EXPECT_EQ(ParamValue(design, "E"), 8);
}

TEST(ConstExprElab, Clog2FoldsAnAllOnesUnsignedArgument) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int A = $clog2(32'hFFFF_FFFF);\n"
      "  localparam int B = $clog2(8'hFF);\n"
      "  localparam int C = $clog2(0);\n"
      "  localparam int D = $clog2(257);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "A"), 32);
  EXPECT_EQ(ParamValue(design, "B"), 8);
  EXPECT_EQ(ParamValue(design, "C"), 0);
  EXPECT_EQ(ParamValue(design, "D"), 9);
}

TEST(ConstExprElab, MathFunctionsSizeARangeAndFoldInAParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [$clog2(256) - 1 : 0] v;\n"
      "  localparam int W = $bits(v);\n"
      "  localparam int F = $floor($sqrt(17.0));\n"
      "  if ($clog2(4) == 2) begin : g\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "W"), 8);
  EXPECT_EQ(ParamValue(design, "F"), 4);
}

TEST(ConstExprElab, DISABLED_ARealMathFunctionSelectsAGenerateBranch) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  if ($pow(2, 3) == 8.0) begin : g\n"
             "  end\n"
             "  case ($sqrt(16.0) > 3)\n"
             "    1: begin : h end\n"
             "    default: begin : k end\n"
             "  endcase\n"
             "endmodule\n"));
}

}  // namespace
