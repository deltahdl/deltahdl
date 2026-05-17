#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaborator, DelayModeUnit_PropagatedToModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_unit\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kUnit);
}

TEST(Elaborator, DelayModeUnit_OverridesPath) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "`delay_mode_unit\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kUnit);
}

}
