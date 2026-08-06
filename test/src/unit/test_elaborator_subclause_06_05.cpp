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

// §6.5: a continuous assignment may drive a variable of any data type, not just
// a packed integral one -- the standard's own example continuously assigns a
// real variable. This exercises the real-operand input form of the
// variable-continuous-assignment rule.
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

// §6.5: the single-driver rule is stated per term of a variable's longest
// static prefix, so two continuous assignments writing the same element are two
// drivers of that term and are illegal -- even though each is a select and so
// escapes the whole-variable name check. Contrast
// VariableDistinctBitsEachSingleContinuousAssignmentOk, where the two selects
// address different bits.
TEST(NetsAndVariables, SamePackedBitMultipleContinuousAssignmentsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic [1:0] v;\n"
      "  assign v[0] = 1'b0;\n"
      "  assign v[0] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.5: the same per-element rule applies to an element of an unpacked array;
// driving one element with two continuous assignments is illegal.
TEST(NetsAndVariables, UnpackedArrayElementMultipleContinuousAssignmentsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  assign mem[0] = 8'd1;\n"
      "  assign mem[0] = 8'd2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.5: distinct elements of an unpacked array have non-overlapping longest
// static prefixes, so each may carry its own single continuous assignment.
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

// §6.5: mixing a continuous assignment with a procedural assignment to the same
// element is illegal. The procedural side here is a general always block, whose
// longest-static-prefix analysis of the select keeps the conflict at bit
// granularity rather than collapsing to the whole variable.
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
  EXPECT_TRUE(f.has_errors);
}

// §6.5 (LRM struct abc example): the standard's own illegal case is two
// continuous assignments to a single structure member. A member access escapes
// the whole-variable name check, so the per-element longest-static-prefix rule
// is what makes the second continuous driver an error.
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
  EXPECT_TRUE(f.has_errors);
}

// §6.5: identifying the driven element by its longest static prefix admits a
// constant-expression select index, not only a literal. A parameter index (a
// constant form of §11.2.1) resolves to a value, so two continuous assignments
// through the same parameter index name the same element and collide -- the
// parameter takes the scope-aware constant-evaluation path, distinct from a
// literal index.
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
  EXPECT_TRUE(f.has_errors);
}

// §6.5: localparam indices (another constant form of §11.2.1) that resolve to
// different values name different elements, whose longest static prefixes do
// not overlap, so each element carries its own single continuous assignment.
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

// §6.5: within a name space it is illegal to redeclare a name already declared
// by a net, variable, or other declaration -- here a variable name reused for a
// net.
TEST(NetsAndVariables, RedeclareVariableAsNetError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  wire v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.5: the redeclaration prohibition is symmetric in the kinds involved -- a
// name first declared as a net cannot be reused for a variable either.
TEST(NetsAndVariables, RedeclareNetAsVariableError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  logic w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.5: connecting a variable to an input port implies a continuous assignment
// to it, which makes any assignment to a variable declared as an input port
// illegal. `var` forces the input port to be a variable rather than the default
// net, so the internal procedural write is a second driver and is rejected.
TEST(NetsAndVariables, VariableInputPortAssignmentError) {
  ElabFixture f;
  Elaborate(
      "module t(input var logic x);\n"
      "  initial x = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.5: data shall be declared before it is used, apart from implicit nets. A
// bare identifier read in a procedural assignment is not an implicit-net
// context, so referencing an undeclared name there is an error.
TEST(NetsAndVariables, UndeclaredDataUsedProcedurallyError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic a;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.5: the declared-before-use rule explicitly exempts implicit nets (§6.10).
// A continuous assignment to an otherwise-undeclared name creates the implicit
// net that the assignment drives, so no prior declaration is required and it
// elaborates cleanly -- the accepting counterpart to
// UndeclaredDataUsedProcedurallyError.
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

}  // namespace
