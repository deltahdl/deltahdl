#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ContinuousAssignDeclElaboration, NetDeclAssignCreatesContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  EXPECT_EQ(mod->nets[0].name, "w");
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_NE(mod->assigns[0].rhs, nullptr);
}

TEST(ContinuousAssignDeclElaboration, NetDeclAssignLhsIsNetName) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire mynet = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns[0];
  ASSERT_NE(ca.lhs, nullptr);
  EXPECT_EQ(ca.lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(ca.lhs->text, "mynet");
}

TEST(ContinuousAssignDeclElaboration, NetDeclAssignWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire [7:0] data = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].width, 8u);
}

TEST(ContinuousAssignDeclElaboration, NetDeclNoInitNoContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->assigns.size(), 0u);
}

TEST(ContinuousAssignDeclElaboration, MultiNetDeclAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire a = 1'b0, b = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 2u);
}

// §10.3.1: the net declaration assignment form is not specific to `wire` -- a
// net declaration on any net type places a continuous assignment on the net.
// Elaborating a `tri` net with an initializer exercises the same
// LowerNetDeclAssignment path with a different declared net type.
TEST(ContinuousAssignDeclElaboration, TriNetDeclAssignCreatesContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  tri w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->nets.size(), 1u);
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_NE(mod->assigns[0].rhs, nullptr);
}

// §10.3.1: mirrors the subclause's own worked example, a net declaration
// assignment carrying a drive strength (`wire (strong1, pull0) mynet = ...`).
// The strength-decorated declaration still lowers to a continuous assignment on
// the net; only the presence of that driver is asserted here (strength
// semantics belong to §10.3.4), confirming the strength does not suppress the
// net declaration assignment.
TEST(ContinuousAssignDeclElaboration, StrengthNetDeclAssignCreatesContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  logic en;\n"
      "  wire (strong1, pull0) mynet = en;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_NE(mod->assigns[0].rhs, nullptr);
}

TEST(ContinuousAssignDeclElaboration, NetDeclAssignConflictsWithProcAssign) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w = 1'b0;\n"
      "  initial w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ContinuousAssignDeclElaboration, InterconnectNetDeclAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  interconnect sig = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §10.3.1: the prohibition is specifically against a *net declaration
// assignment* on an interconnect net -- a bare interconnect declaration with no
// initializer is legal. Elaborating the same net without the `= 1` initializer
// clean isolates the assignment as the trigger for the error above, confirming
// LowerNetDeclAssignment's interconnect check (not something incidental about
// interconnect nets) is what fires.
TEST(ContinuousAssignDeclElaboration, InterconnectNetDeclNoAssignIsOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  interconnect sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §10.3.1: the interconnect prohibition is independent of the net's shape -- a
// vector (packed) interconnect net with an initializer is rejected exactly as
// the scalar form is. Building the interconnect from real `interconnect [3:0]`
// syntax confirms the §6.6.8 dependency's packed form still trips the rule.
TEST(ContinuousAssignDeclElaboration, InterconnectVectorNetDeclAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  interconnect [3:0] sig = 4'd1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
