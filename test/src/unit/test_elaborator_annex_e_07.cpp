#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §E.7: delay_mode_zero propagates to elaborated module.
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

// §E.7: last delay mode directive wins.
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

}  // namespace
