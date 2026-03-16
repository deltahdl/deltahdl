#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(IfdefElaboration, IfdefSelectsParameterValueForElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define USE_WIDE\n"
      "module t;\n"
      "`ifdef USE_WIDE\n"
      "  parameter P = 32;\n"
      "`else\n"
      "  parameter P = 8;\n"
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

TEST(IfdefElaboration, IfdefElseBranchElaboratesWhenUndefined) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "`ifdef USE_WIDE\n"
      "  parameter P = 32;\n"
      "`else\n"
      "  parameter P = 8;\n"
      "`endif\n"
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

TEST(IfdefElaboration, ElsifChainSelectsCorrectValueForElaboration) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`define MODE_B\n"
      "module t;\n"
      "`ifdef MODE_A\n"
      "  parameter P = 1;\n"
      "`elsif MODE_B\n"
      "  parameter P = 2;\n"
      "`else\n"
      "  parameter P = 3;\n"
      "`endif\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 2);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(IfdefElaboration, IfndefElaboratesWhenUndefined) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module t;\n"
      "`ifndef MISSING\n"
      "  parameter P = 42;\n"
      "`else\n"
      "  parameter P = 0;\n"
      "`endif\n"
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
