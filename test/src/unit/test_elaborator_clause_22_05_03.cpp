#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(UndefineAllElaboration, UndefineAllThenRedefineElaboratesNewValue) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define WIDTH 8\n"
      "`undefineall\n"
      "`define WIDTH 32\n"
      "module t;\n"
      "  parameter P = `WIDTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 32);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UndefineAllElaboration, UndefineAllExcludesConditionalFromElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define USE_WIDE\n"
      "`undefineall\n"
      "module t;\n"
      "`ifdef USE_WIDE\n"
      "  parameter P = 64;\n"
      "`else\n"
      "  parameter P = 16;\n"
      "`endif\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 16);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
