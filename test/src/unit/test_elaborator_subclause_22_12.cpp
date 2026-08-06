#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §22.12: the `line directive shall set the line number of the following line.
// To observe that renumbering being applied at elaboration time we fold the
// current line - read back through `__LINE__ - into a packed dimension and
// check the resulting vector width. The width equals the overridden number, not
// the natural source line, so the assertion discriminates whether the `line
// rule was actually applied by the preprocessor before elaboration.

TEST(LineDirectiveElaboration, OverriddenLineSizesElaboratedVector) {
  ElabFixture f;
  // `line is on source line 2; the following line reports exactly 40, so the
  // vector [40-1:0] elaborates to 40 bits (the natural line would give 3).
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
  // The directive on source line 4 renumbers the rest: `__LINE__ on source line
  // 6 reports 60 + (6 - 4 - 1) == 61, giving a 61-bit vector.
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
