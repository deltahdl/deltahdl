#include "fixture_elaborator.h"

using namespace delta;

namespace {

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

TEST(NetsAndVariables, NetCannotBeProcedurallyAssigned) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  initial w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(NetsAndVariables, NetMultipleContinuousAssignmentsOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign w = 1'b0;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetsAndVariables, VariableInitPlusContinuousAssignmentOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic v = 1'b1;\n"
      "  assign v = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
