#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveElaboration, DirectiveScopeAffectsElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define WIDTH 16\n"
      "module t;\n"
      "  parameter W = `WIDTH;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "W") {
      EXPECT_EQ(p.resolved_value, 16);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(CompilerDirectiveElaboration, DirectiveSupersededBeforeElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define VAL 10\n"
      "`define VAL 20\n"
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
      EXPECT_EQ(p.resolved_value, 20);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(CompilerDirectiveElaboration, DirectiveInConditionalAffectsElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define FEATURE 1\n"
      "`ifdef FEATURE\n"
      "`define SIZE 32\n"
      "`else\n"
      "`define SIZE 8\n"
      "`endif\n"
      "module t;\n"
      "  parameter S = `SIZE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "S") {
      EXPECT_EQ(p.resolved_value, 32);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(CompilerDirectiveElaboration, DirectiveInCommentDoesNotAffectElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define VAL 42\n"
      "// `define VAL 99\n"
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
      EXPECT_EQ(p.resolved_value, 42);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
