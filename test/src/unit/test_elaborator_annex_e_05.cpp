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

// Claim A edge case ("all modules that follow"): a single directive selects the
// path delay mode for every module that comes after it, not just the first. Both
// modules elaborated below should carry the path mode.
TEST(Elaborator, DelayModePath_AppliesToAllFollowingModules) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "module a;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kPath);
  EXPECT_EQ(design->top_modules[1]->delay_mode, DelayModeDirective::kPath);
}

}
