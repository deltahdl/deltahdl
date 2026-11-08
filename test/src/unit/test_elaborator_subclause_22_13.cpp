#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(FileAndLineMacroElaboration, LineDecimalSizesElaboratedVector) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  logic a;\n"
      "  logic [`__LINE__ - 1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[1].name, "wide");
  EXPECT_EQ(mod->variables[1].width, 3u);
}

TEST(FileAndLineMacroElaboration, LineDecimalTracksSourceLine) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "  logic a;\n"
      "  logic b;\n"
      "  logic [`__LINE__ - 1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[2].name, "wide");
  EXPECT_EQ(mod->variables[2].width, 4u);
}

}  // namespace
