#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(RealConversion, IntParameterFromRealLiteralRounds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 35.7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "P");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 36);
}

TEST(RealConversion, IntParameterRealTieRoundsAwayFromZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 2.5;\n"
      "  parameter int Q = -1.5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->params[0].resolved_value, 3);
  EXPECT_EQ(design->top_modules[0]->params[1].resolved_value, -2);
}

TEST(RealConversion, IntLocalparamFromRealLiteralRounds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int L = 2.5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& l = design->top_modules[0]->params[0];
  EXPECT_EQ(l.name, "L");
  EXPECT_TRUE(l.is_resolved);
  EXPECT_EQ(l.resolved_value, 3);
}

TEST(RealConversion, RangedParameterFromRealLiteralRounds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter [7:0] R = 35.5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& r = design->top_modules[0]->params[0];
  EXPECT_EQ(r.name, "R");
  EXPECT_TRUE(r.is_resolved);
  EXPECT_EQ(r.resolved_value, 36);
}

}  // namespace
