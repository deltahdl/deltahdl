#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaborator, DelayModeZero_PropagatedToModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_zero\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kZero);
}

TEST(Elaborator, DelayModeZero_OverridesUnit) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_unit\n"
      "`delay_mode_zero\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kZero);
}

// C1 (edge, negative control): the zero delay mode reaches a module only
// because the directive selected it. With no directive ahead of the module,
// elaboration leaves the module's delay mode unset, confirming `delay_mode_zero
// is what drives the kZero result above rather than a default.
TEST(Elaborator, DelayModeZero_AbsentLeavesModeUnset) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kNone);
}

}  // namespace
