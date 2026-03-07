#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.8/§6.20.6: Const variable must have an initializer.
TEST(VarDecl, ConstWithoutInitializerIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  const int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.8/§6.20.6: Const variable with initializer is valid.
TEST(VarDecl, ConstWithInitializerOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  const int MAX = 100;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.8: Redeclaration of the same name is an error.
TEST(VarDecl, RedeclarationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.8: Variable with initializer produces correct RTLIR.
TEST(VarDecl, InitializerPreservedInRtlir) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_NE(mod->variables[0].init_expr, nullptr);
}

// §6.8: 4-state type (logic) is correctly identified.
TEST(VarDecl, LogicIs4State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_4state);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

// §6.8: 2-state type (int) is correctly identified.
TEST(VarDecl, IntIs2State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int count;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->variables[0].is_4state);
  EXPECT_EQ(mod->variables[0].width, 32u);
}

// §6.8: Signed type (int) is correctly identified.
TEST(VarDecl, IntIsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_signed);
}

// §6.8: Real variable is correctly identified.
TEST(VarDecl, RealIsReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real voltage;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_real);
}

// §6.8: String variable is correctly identified.
TEST(VarDecl, StringIsString) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  string name;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_string);
}

// §6.8: Event variable is correctly identified.
TEST(VarDecl, EventIsEvent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event done;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  EXPECT_TRUE(mod->variables[0].is_event);
}

// §6.8: Multiple variable declarations produce multiple RTLIR variables.
TEST(VarDecl, MultipleVarsInOneStatement) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].name, "t.a");
  EXPECT_EQ(mod->variables[1].name, "t.b");
  EXPECT_EQ(mod->variables[2].name, "t.c");
}

}  // namespace
