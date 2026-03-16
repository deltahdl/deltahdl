#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ResetAllElaboration, ResetsDelayModeForElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_zero\n"
      "`resetall\n"
      "module t;\n"
      "  parameter P = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kNone);
}

TEST(ResetAllElaboration, PreservesMacroValuesForElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define VAL 55\n"
      "`resetall\n"
      "module t;\n"
      "  parameter P = `VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 55);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ResetAllElaboration, BetweenModulesResetsDelayModeForElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_path\n"
      "module m1;\n"
      "  parameter P = 1;\n"
      "endmodule\n"
      "`resetall\n"
      "module m2;\n"
      "  parameter Q = 2;\n"
      "endmodule\n",
      f, "m2");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kNone);
}

TEST(ResetAllElaboration, InsideExcludedBranchDoesNotAffectElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`delay_mode_unit\n"
      "`ifdef UNDEF\n"
      "`resetall\n"
      "`endif\n"
      "module t;\n"
      "  parameter P = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->delay_mode, DelayModeDirective::kUnit);
}

}  // namespace
