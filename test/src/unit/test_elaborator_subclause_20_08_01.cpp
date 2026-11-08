#include <gtest/gtest.h>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

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

}  // namespace
