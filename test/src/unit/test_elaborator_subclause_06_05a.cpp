#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

TEST(NetsAndVariables, RealVariableContinuousAssignmentOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  real circ;\n"
      "  assign circ = 3.14;\n"
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "multiple continuous assignments to 'v'", 4,
                            "6.5"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' has both continuous and procedural assignments", 4, "6.5"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'w' cannot be the target of a procedural assignment", 3, "10.4"));
}

TEST(NetsAndVariables, VariableInitializerPlusContinuousAssignmentError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v = 1'b0;\n"
      "  assign v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' has both an initializer and a continuous assignment", 3,
      "10.3.2"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' driven by both output port and continuous assignment", 6,
      "6.5"));
}

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'v' driven by output port has procedural assignments", 6,
      "6.5"));
}

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

TEST(NetsAndVariables, SamePackedBitMultipleContinuousAssignmentsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic [1:0] v;\n"
      "  assign v[0] = 1'b0;\n"
      "  assign v[0] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "multiple continuous assignments drive overlapping element 'v[0]'", 4,
      "6.5"));
}

TEST(NetsAndVariables, UnpackedArrayElementMultipleContinuousAssignmentsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  assign mem[0] = 8'd1;\n"
      "  assign mem[0] = 8'd2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "multiple continuous assignments drive overlapping element 'mem[0]'", 4,
      "6.5"));
}

TEST(NetsAndVariables, UnpackedArrayDistinctElementsContinuousAssignmentsOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  assign mem[0] = 8'd1;\n"
      "  assign mem[1] = 8'd2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetsAndVariables, PackedBitContinuousAndProceduralError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic clk;\n"
      "  logic [1:0] v;\n"
      "  assign v[0] = 1'b0;\n"
      "  always @(posedge clk) v[0] <= 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "element 'v[0]' has both a continuous assignment "
                            "and a procedural assignment",
                            4, "10.3.2"));
}

TEST(NetsAndVariables, StructMemberMultipleContinuousAssignmentsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "    logic [7:0] c;\n"
      "  } abc_t;\n"
      "  abc_t abc;\n"
      "  assign abc.c = 8'hef;\n"
      "  assign abc.c = 8'hed;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "multiple continuous assignments drive overlapping element 'abc.c'", 9,
      "6.5"));
}

TEST(NetsAndVariables,
     ParameterIndexedElementMultipleContinuousAssignmentsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  parameter P = 0;\n"
      "  logic [1:0] v;\n"
      "  assign v[P] = 1'b0;\n"
      "  assign v[P] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "multiple continuous assignments drive overlapping element 'v[0]'", 5,
      "6.5"));
}

TEST(NetsAndVariables,
     LocalparamIndexedDistinctElementsContinuousAssignmentsOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  localparam A = 0;\n"
      "  localparam B = 1;\n"
      "  logic [1:0] v;\n"
      "  assign v[A] = 1'b0;\n"
      "  assign v[B] = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetsAndVariables, RedeclareVariableAsNetError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  wire v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'v'", 3, "6.5"));
}

TEST(NetsAndVariables, RedeclareNetAsVariableError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  logic w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'w'", 3, "6.5"));
}

TEST(NetsAndVariables, VariableInputPortAssignmentError) {
  ElabFixture f;
  Elaborate(
      "module t(input var logic x);\n"
      "  initial x = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'x' is declared as an input port and "
                            "cannot be the target of an assignment",
                            2, "23.3.3.2"));
}

TEST(NetsAndVariables, UndeclaredDataUsedProcedurallyError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic a;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'b'", 3,
                            "23.9"));
}

TEST(NetsAndVariables, ImplicitNetFromContinuousAssignNeedsNoDeclarationOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  assign w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetsAndVariables, ContinuousAndAlwaysCombAssignmentsToOneVariableError) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  logic a;\n"
      "  logic y;\n"
      "  assign y = a;\n"
      "  always_comb y = ~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'y' has both continuous and procedural assignments", 4, "6.5"));
}

TEST(NetsAndVariables, NetAssignedFromAlwaysCombError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  always_comb w = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'w' cannot be the target of a procedural assignment", 3, "10.4"));
}

TEST(NetsAndVariables, NetAssignedFromFinalError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  final w = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'w' cannot be the target of a procedural assignment", 3, "10.4"));
}

TEST(NetsAndVariables, ContinuousAndAlwaysFfAssignmentsToOneVariableError) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  logic clk;\n"
      "  logic a;\n"
      "  logic y;\n"
      "  assign y = a;\n"
      "  always_ff @(posedge clk) y <= a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'y' has both continuous and procedural assignments", 5, "6.5"));
}

TEST(NetsAndVariables, ProceduralAssignmentInAForkMixesWithAContinuousAssign) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial fork\n"
      "    x = 1'b1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'x' has both continuous and procedural assignments", 3, "6.5"));
}

TEST(NetsAndVariables, ProceduralAssignmentInARandcaseArmMixesWithAContAssign) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial randcase\n"
      "    1 : x = 1'b1;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'x' has both continuous and procedural assignments", 3, "6.5"));
}

TEST(NetsAndVariables, ProceduralAssignmentInAForInitMixesWithAContAssign) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  logic x;\n"
      "  logic [7:0] i;\n"
      "  assign x = 1'b0;\n"
      "  initial for (x = 1'b1; i < 2; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'x' has both continuous and procedural assignments", 4, "6.5"));
}

TEST(NetsAndVariables, ProceduralAssignmentInAForStepMixesWithAContAssign) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  logic x;\n"
      "  logic [7:0] i;\n"
      "  assign x = 1'b0;\n"
      "  initial for (i = 0; i < 2; x = 1'b1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'x' has both continuous and procedural assignments", 4, "6.5"));
}

TEST(NetsAndVariables,
     ProceduralAssignmentInAnAssertPassArmMixesWithAContAssign) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial assert (1) x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'x' has both continuous and procedural assignments", 3, "6.5"));
}

TEST(NetsAndVariables,
     ProceduralAssignmentInAnAssertFailArmMixesWithAContAssign) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial assert (0) else x = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'x' has both continuous and procedural assignments", 3, "6.5"));
}

TEST(NetsAndVariables, ProceduralAssignmentToANetInAForkIsRejected) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  wire w;\n"
      "  initial fork\n"
      "    w = 1'b1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'w' cannot be the target of a procedural assignment", 4, "10.4"));
}

TEST(NetsAndVariables, AProceduralAssignmentInAForkAloneIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  logic x;\n"
      "  initial fork\n"
      "    x = 1'b1;\n"
      "  join\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetsAndVariables,
     ProceduralAssignmentInARandsequenceMixesWithAContAssign) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = 1'b1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'x' has both continuous and procedural assignments", 3, "6.5"));
}

TEST(NetsAndVariables,
     ProceduralAssignmentInARandsequenceWeightBlockMixesWithAContAssign) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  logic x;\n"
      "  assign x = 1'b0;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : a := 5 { x = 1'b1; };\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "variable 'x' has both continuous and procedural assignments", 3, "6.5"));
}

TEST(NetsAndVariables, ProceduralAssignmentToANetInARandsequenceIsRejected) {
  ElabFixture f;
  Elaborate(
      "module top();\n"
      "  wire w;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { w = 1'b1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "net 'w' cannot be the target of a procedural assignment", 5, "10.4"));
}

TEST(NetsAndVariables, AProceduralAssignmentInARandsequenceAloneIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  logic x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = 1'b1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
