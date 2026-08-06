#include "fixture_elaborator.h"

using namespace delta;

namespace {

// WITNESS is never defined again, so the `ifdef is what proves the removal:
// redefining WIDTH on its own would yield 32 even if the directive did nothing.
TEST(UndefineAllElaboration, UndefineAllThenRedefineElaboratesNewValue) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define WIDTH 8\n"
      "`define WITNESS\n"
      "`undefineall\n"
      "`define WIDTH 32\n"
      "module t;\n"
      "`ifdef WITNESS\n"
      "  parameter P = 99;\n"
      "`else\n"
      "  parameter P = `WIDTH;\n"
      "`endif\n"
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

// The directive sits inside the module body — §22.5.3 places no restriction on
// where it appears — and the macro it removed no longer selects a branch, so
// the design elaborates from the `else arm.
TEST(UndefineAllElaboration, UndefineAllInsideDesignElementRemovesMacros) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define USE_WIDE\n"
      "module t;\n"
      "`undefineall\n"
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

// A `undefineall in a branch the conditional excluded is not part of the
// compilation unit, so the macro survives and still picks the wide parameter.
TEST(UndefineAllElaboration, UndefineAllInFalseBranchLeavesMacroDefined) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define USE_WIDE\n"
      "`ifdef NEVER_DEFINED\n"
      "`undefineall\n"
      "`endif\n"
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
      EXPECT_EQ(p.resolved_value, 64);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
