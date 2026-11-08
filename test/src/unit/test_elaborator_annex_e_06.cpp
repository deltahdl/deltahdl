#include <gtest/gtest.h>

#include <string_view>

#include "common/types.h"
#include "elaborator/rtlir.h"
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

TEST(Elaborator, DelayModeUnit_AbsentLeavesModeUnset) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kNone);
}

DelayModeDirective UnitCaseDelayMode(const RtlirDesign* design,
                                     std::string_view module) {
  for (const auto* mod : design->top_modules) {
    if (mod->name == module) return mod->delay_mode;
  }
  return DelayModeDirective::kNone;
}

TEST(Elaborator, DelayModeUnit_LeavesAModuleDeclaredBeforeItUnset) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module ahead;\n"
      "endmodule\n"
      "`delay_mode_unit\n"
      "module behind;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(UnitCaseDelayMode(design, "ahead"), DelayModeDirective::kNone);
  EXPECT_EQ(UnitCaseDelayMode(design, "behind"), DelayModeDirective::kUnit);
}

TEST(Elaborator, DelayModeUnit_ControlsOnlyTheModulesAfterIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "module routed;\n"
      "endmodule\n"
      "`delay_mode_unit\n"
      "module stepped;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(UnitCaseDelayMode(design, "routed"), DelayModeDirective::kPath);
  EXPECT_EQ(UnitCaseDelayMode(design, "stepped"), DelayModeDirective::kUnit);
}

}  // namespace
