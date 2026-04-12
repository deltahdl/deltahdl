#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(VarDeclAssignmentElaboration, VariableInitIsNotContinuousAssignment) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic v = 1'b1;\n"
      "  always_comb v = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VarDeclAssignmentElaboration, InitPreservedAsVariableNotContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [7:0] v = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& var : mod->variables) {
    if (var.name == "v") {
      found = true;
      EXPECT_NE(var.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
  EXPECT_TRUE(mod->assigns.empty());
}

TEST(VarDeclAssignmentElaboration, InitWithProceduralDriverOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  int x = 10;\n"
      "  initial x = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(VarDeclAssignmentElaboration, MultipleVarsWithInitAllPreserved) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  int a = 1, b = 2, c = 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int init_count = 0;
  for (const auto& var : mod->variables) {
    if (var.init_expr) init_count++;
  }
  EXPECT_EQ(init_count, 3);
}

TEST(VarDeclAssignmentElaboration, StaticClassMemberWithInitElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "class C;\n"
      "  static int val = 42;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = C::val;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
