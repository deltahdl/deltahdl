#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DefineElaboration, MacroDefinedParameterElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define WIDTH 16\n"
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
      EXPECT_EQ(p.resolved_value, 16);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(DefineElaboration, FunctionLikeMacroElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define DOUBLE(x) (x * 2)\n"
      "module t;\n"
      "  parameter P = `DOUBLE(11);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 22);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(DefineElaboration, RedefinedMacroUsesLatestValueForElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define VAL 10\n"
      "`define VAL 30\n"
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
      EXPECT_EQ(p.resolved_value, 30);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(DefineElaboration, NestedMacroElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define INNER 5\n"
      "`define OUTER (`INNER + 3)\n"
      "module t;\n"
      "  parameter P = `OUTER;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 8);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(DefineElaboration, MacroWithDefaultArgElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define ADD(a, b=100) (a + b)\n"
      "module t;\n"
      "  parameter P = `ADD(1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 101);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
