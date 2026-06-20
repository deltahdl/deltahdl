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

// §6.5: a declared variable initialization counts as a procedural assignment
// for the single-driver rule, so combining it with a continuous assignment to
// the same variable is illegal.
TEST(NetsAndVariables, VariableInitializerPlusContinuousAssignmentError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v = 1'b0;\n"
      "  assign v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.5: an initialization alone is the variable's single driver and is legal;
// only adding a second (continuous) driver triggers the error above.
TEST(NetsAndVariables, VariableInitializerAloneOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic v = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.5: connecting a variable to the output port of an instance implies a
// continuous assignment to that variable. That implied driver is itself the
// variable's single legal driver, so the connection alone elaborates cleanly.
TEST(NetsAndVariables, VariableOnInstanceOutputPortAloneOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child(output o);\n"
      "  assign o = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  logic v;\n"
      "  child c(.o(v));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.5: because the output-port connection already implies a continuous
// assignment, an additional continuous assignment to the same variable is a
// second driver and is illegal.
TEST(NetsAndVariables, VariableOnInstanceOutputPortPlusContinuousAssignError) {
  ElabFixture f;
  Elaborate(
      "module child(output o);\n"
      "  assign o = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  logic v;\n"
      "  child c(.o(v));\n"
      "  assign v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.5: likewise, a procedural assignment to a variable already driven through
// an instance output-port connection is illegal.
TEST(NetsAndVariables, VariableOnInstanceOutputPortPlusProceduralAssignError) {
  ElabFixture f;
  Elaborate(
      "module child(output o);\n"
      "  assign o = 1'b0;\n"
      "endmodule\n"
      "module top;\n"
      "  logic v;\n"
      "  child c(.o(v));\n"
      "  initial v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.5: each bit of a packed variable is an independent element. Distinct bits
// may therefore each carry their own continuous assignment; the single-driver
// rule applies per longest-static-prefix term, not to the whole variable, so
// this is legal (contrast VariableMultipleContinuousAssignmentsError, which
// drives the same whole variable twice).
TEST(NetsAndVariables, VariableDistinctBitsEachSingleContinuousAssignmentOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [1:0] v;\n"
      "  assign v[0] = 1'b0;\n"
      "  assign v[1] = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §6.5: independent elements are examined individually, so one element of a
// variable may be driven continuously while a different element is driven
// procedurally without violating the single-driver rule.
TEST(NetsAndVariables, VariableDistinctBitsContinuousAndProceduralOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [1:0] v;\n"
      "  assign v[0] = 1'b0;\n"
      "  initial v[1] = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
