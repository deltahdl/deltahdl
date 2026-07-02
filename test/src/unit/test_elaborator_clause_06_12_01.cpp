#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.12.1's conversion also applies at elaboration when a real constant
// initializes an integer-typed parameter: the value is rounded to the nearest
// integer, not truncated. 35.7 truncates to 35 but rounds to 36, so this
// observes the elaborator's round-to-nearest path (not a bit copy).
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

// The exact-half tie rounds away from zero in both directions at elaboration:
// 2.5 -> 3 (discriminating round-half-to-even's 2) and -1.5 -> -2.
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

// A localparam is a distinct declaration form but is subject to the same
// real-to-integer rounding when it carries an integer type. 2.5 -> 3.
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

// A parameter placed in an integer context by a packed range (rather than an
// explicit integer keyword) reaches the conversion through a different branch;
// the rounding rule still applies: 35.5 -> 36.
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
