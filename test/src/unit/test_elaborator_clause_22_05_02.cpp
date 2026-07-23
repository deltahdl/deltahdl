#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(UndefElaboration, UndefThenRedefineUsesNewValueForElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define WIDTH 8\n"
      "`undef WIDTH\n"
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

TEST(UndefElaboration, UndefExcludesConditionalCodeFromElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define USE_WIDE\n"
      "`undef USE_WIDE\n"
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

// A macro removed by `undef has no value, so the parameter that elaborates
// here comes entirely from the definition made after the removal — the formal
// argument list of the discarded definition leaves nothing behind.
TEST(UndefElaboration, RedefineAfterUndefDropsFormalArgumentsForElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define M(a,b) ((a)+(b))\n"
      "`undef M\n"
      "`define M 24\n"
      "module t;\n"
      "  parameter P = `M;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 24);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UndefElaboration, UndefDoesNotAffectOtherMacroElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define A 10\n"
      "`define B 20\n"
      "`undef A\n"
      "module t;\n"
      "  parameter P = `B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 20);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
