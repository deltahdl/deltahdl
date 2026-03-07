#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.5: Two main groups of data objects: variables and nets.
TEST(NetsAndVariables, NetElaboratedAsNet) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].name, "w");
}

TEST(NetsAndVariables, VariableElaboratedAsVariable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "v") found = true;
  }
  EXPECT_TRUE(found);
}

// §6.5: A net can be written by one or more continuous assignments.
TEST(NetsAndVariables, NetWithContinuousAssignment) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_GE(mod->assigns.size(), 1u);
}

// §6.5: Variable can be written by one continuous assignment.
TEST(NetsAndVariables, VariableOneContinuousAssignmentOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic vw;\n"
      "  assign vw = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.5: Error — multiple continuous assignments to the same variable.
TEST(NetsAndVariables, VariableMultipleContinuousAssignmentsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  assign v = 1'b0;\n"
      "  assign v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.5: Error — mixing continuous and procedural assignments to a variable.
TEST(NetsAndVariables, VariableMixedContinuousAndProceduralError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  wire clk = 0;\n"
      "  int v;\n"
      "  assign v = 12;\n"
      "  always @(posedge clk) v <= ~v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.5: Variable initialization is NOT a continuous assignment.
// logic v = expr is an initialization, not continuous assignment.
TEST(NetsAndVariables, VariableInitIsNotContinuousAssignment) {
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

// §6.5: Net with implicit continuous assignment (net declaration assignment).
// wire w = expr creates a continuous assignment.
TEST(NetsAndVariables, NetDeclAssignmentIsContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
}

// §6.5: Illegal to redeclare a name already declared by a net, variable, or
// other declaration in the same name space.
TEST(NetsAndVariables, RedeclarationOfVariableAsNetError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  reg v;\n"
      "  wire v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(NetsAndVariables, RedeclarationOfNetAsVariableError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  wire w;\n"
      "  logic w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(NetsAndVariables, RedeclarationOfVariableError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int x;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.5: Variables can be written by procedural statements; last write wins.
TEST(NetsAndVariables, VariableProceduralAssignmentOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  initial v = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.5: Multiple procedural assignments to the same variable are OK.
TEST(NetsAndVariables, VariableMultipleProceduralAssignmentsOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    v = 1'b0;\n"
      "    v = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.5: Different variables can have different assignment modes.
TEST(NetsAndVariables, SeparateVarsContAndProcOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic a, b;\n"
      "  assign a = 1'b1;\n"
      "  initial b = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.5: Net redeclaration error.
TEST(NetsAndVariables, RedeclarationOfNetError) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  wire w;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
