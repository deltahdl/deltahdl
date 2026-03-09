#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaborator, DelayModePath_PropagatedToModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kPath);
}

TEST(Elaborator, DelayModePath_OverridesDistributed) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_distributed\n"
      "`delay_mode_path\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kPath);
}

}  // namespace
