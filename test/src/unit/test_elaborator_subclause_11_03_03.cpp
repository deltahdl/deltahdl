#include <gtest/gtest.h>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(IntegerLiteralElaboration, NegatedUnbasedDivThreeEqualsMinusFour) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), -4);
}

TEST(IntegerLiteralElaboration, NegatedUnsignedBasedDivThree) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-'d12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), 1431655761);
}

TEST(IntegerLiteralElaboration, NegatedSignedBasedDivThreeEqualsMinusFour) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-'sd12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), -4);
}

TEST(IntegerLiteralElaboration, NegatedSizedSignedBasedDivThreeEqualsOne) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-4'sd12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), 1);
}

TEST(IntegerLiteralElaboration, NegatedSizedUnsignedBasedDivThree) {
  EvalFixture f;
  auto val = ConstEvalInt(ParseExprFrom("-32'd12 / 3", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), 1431655761);
}

TEST(IntegerLiteralElaboration, ParameterUnsignedBasedLiteralResolvesUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = -'d12 / 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 1431655761);
}

TEST(IntegerLiteralElaboration, LocalparamUnbasedLiteralResolvesSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int Q = -12 / 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& q = design->top_modules[0]->params[0];
  EXPECT_EQ(q.name, "Q");
  EXPECT_TRUE(q.is_resolved);
  EXPECT_EQ(q.resolved_value, -4);
}

}  // namespace
