#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(LineDirectiveElaboration, OverriddenLineSizesElaboratedVector) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  `line 40 \"renamed.sv\" 0\n"
      "  logic [`__LINE__ - 1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 40u);
}

TEST(LineDirectiveElaboration,
     OverrideBetweenModulesRenumbersElaboratedVector) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module m1;\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "`line 60 \"switched.sv\" 0\n"
      "module t;\n"
      "  logic [`__LINE__ - 1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 61u);
}

}  // namespace
