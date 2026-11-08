#include <gtest/gtest.h>

#include <string_view>

#include "common/types.h"
#include "elaborator/rtlir.h"
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

DelayModeDirective ZeroCaseDelayMode(const RtlirDesign* design,
                                     std::string_view module) {
  for (const auto* mod : design->top_modules) {
    if (mod->name == module) return mod->delay_mode;
  }
  return DelayModeDirective::kNone;
}

TEST(Elaborator, DelayModeZero_LeavesAModuleDeclaredBeforeItUnset) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module upstream;\n"
      "endmodule\n"
      "`delay_mode_zero\n"
      "module downstream;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(ZeroCaseDelayMode(design, "upstream"), DelayModeDirective::kNone);
  EXPECT_EQ(ZeroCaseDelayMode(design, "downstream"), DelayModeDirective::kZero);
}

TEST(Elaborator, DelayModeZero_ControlsOnlyTheModulesAfterIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_unit\n"
      "module ticking;\n"
      "endmodule\n"
      "`delay_mode_zero\n"
      "module instant;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(ZeroCaseDelayMode(design, "ticking"), DelayModeDirective::kUnit);
  EXPECT_EQ(ZeroCaseDelayMode(design, "instant"), DelayModeDirective::kZero);
}

}  // namespace
