#include <gtest/gtest.h>

#include <string_view>

#include "common/types.h"
#include "elaborator/rtlir.h"
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

TEST(Elaborator, DelayModePath_AppliesToAllFollowingModules) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "module a;\n"
      "endmodule\n"
      "module b;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kPath);
  EXPECT_EQ(design->top_modules[1]->delay_mode, DelayModeDirective::kPath);
}

DelayModeDirective TopDelayMode(const RtlirDesign* design,
                                std::string_view module) {
  for (const auto* mod : design->top_modules) {
    if (mod->name == module) return mod->delay_mode;
  }
  return DelayModeDirective::kNone;
}

TEST(Elaborator, DelayModePath_LeavesAModuleDeclaredBeforeItUnset) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module first;\n"
      "endmodule\n"
      "`delay_mode_path\n"
      "module second;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(TopDelayMode(design, "first"), DelayModeDirective::kNone);
  EXPECT_EQ(TopDelayMode(design, "second"), DelayModeDirective::kPath);
}

TEST(Elaborator, DelayModePath_ControlsOnlyTheModulesAfterIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_distributed\n"
      "module spread;\n"
      "endmodule\n"
      "`delay_mode_path\n"
      "module pathed;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(TopDelayMode(design, "spread"), DelayModeDirective::kDistributed);
  EXPECT_EQ(TopDelayMode(design, "pathed"), DelayModeDirective::kPath);
}

}  // namespace
