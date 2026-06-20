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

// §10.5 draws the net-vs-variable distinction directly: an identically
// written `= expr` makes a net a continuously assigned net but makes a
// variable an initialization. Even when a continuous assignment is present
// in the module, the variable's initializer must not be swept into the
// continuous-assignment list; it stays an initializer on the variable.
TEST(VarDeclAssignmentElaboration, NetVsVariableDeclAssignmentDistinction) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  wire [7:0] w = a & b;\n"
      "  logic [7:0] v = a & b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];

  bool var_has_init = false;
  for (const auto& var : mod->variables) {
    if (var.name == "v") var_has_init = (var.init_expr != nullptr);
  }
  EXPECT_TRUE(var_has_init);

  bool assign_targets_var = false;
  for (const auto& ca : mod->assigns) {
    if (ca.lhs && ca.lhs->kind == ExprKind::kIdentifier &&
        ca.lhs->text == "v") {
      assign_targets_var = true;
    }
  }
  EXPECT_FALSE(assign_targets_var);
}

}  // namespace
