#include <gtest/gtest.h>

#include "elaborator/property_rewrite.h"
#include "elaborator/sampled_value.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

// §16.12 forbids nested disable iff clauses. A.2.10's property_spec takes
// one, so the parser reports the second where it stands, and the elaborator
// still counts both.
TEST(PropertyDeclarationElaboration, ExplicitDisableIffNestingRejected) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m(input logic clk, r1, r2, a, b);\n"
      "  property bad;\n"
      "    @(posedge clk) disable iff (r1) disable iff (r2) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "this declaration's body is not one the grammar "
                            "admits",
                            3, "A.2.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"bad\" nests disable iff clauses", 2,
                            "16.12"));
}

// §16.12 forbids disable iff nesting that arises through property
// instantiation: one disable iff in the outer body plus one inside an
// instantiated callee makes two in the flattened form.
TEST(PropertyDeclarationElaboration,
     DisableIffNestingViaInstantiationRejected) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2);\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 5,
                            "16.12"));
}

// §16.12 permits exactly one disable iff in a property_spec.
TEST(PropertyDeclarationElaboration, SingleDisableIffNotFlaggedAsNested) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, rst, a, b);\n"
      "  property ok;\n"
      "    @(posedge clk) disable iff (rst) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12: the no-nesting rule sees disable iff clauses that accumulate across a
// multi-level instantiation chain. root carries one and the transitively
// instantiated leaf carries another, with an intermediate property between
// them; the flattened form has two, so it is rejected.
TEST(PropertyDeclarationElaboration,
     DisableIffNestingViaChainedInstantiationRejected) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2);\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property mid;\n"
      "    @(posedge clk) leaf();\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) disable iff (r2) mid();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 8,
                            "16.12"));
}

// §16.12: two sibling instantiations each contribute a disable iff to the same
// flattened property even though the instantiating property has none of its
// own. Their counts add to two, so the enclosing property is rejected.
TEST(PropertyDeclarationElaboration,
     TwoSiblingDisableIffLeavesUnderOneRootRejected) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clk, r1, a, b, r2, c, d);\n"
      "  property l1;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property l2;\n"
      "    @(posedge clk) disable iff (r2) c |-> d;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) l1() and l2();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "property \"root\" nests disable iff clauses", 8,
                            "16.12"));
}

// §16.12: the count is per flattened property, not per module. Two unrelated
// properties that each carry exactly one disable iff and do not instantiate one
// another are both legal.
TEST(PropertyDeclarationElaboration,
     IndependentSingleDisableIffPropertiesAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, r1, a, b, r2, c, d);\n"
      "  property p1;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property p2;\n"
      "    @(posedge clk) disable iff (r2) c |-> d;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12: a single disable iff that reaches a property purely through one
// instantiation (the instantiating property has none of its own) flattens to a
// count of one and is accepted.
TEST(PropertyDeclarationElaboration, SingleDisableIffViaInstantiationAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, r1, a, b);\n"
      "  property leaf;\n"
      "    @(posedge clk) disable iff (r1) a |-> b;\n"
      "  endproperty\n"
      "  property root;\n"
      "    @(posedge clk) leaf();\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §16.12 head: a sampled value function other than $sampled used in a disable
// condition requires an explicit clock argument; $sampled does not.
TEST(PropertyDeclarationElaboration, DisableConditionSampledValueNeedsClock) {
  // $sampled is well-formed with or without an explicit clock.
  EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, /*clock_explicitly_specified=*/false));
  EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, /*clock_explicitly_specified=*/true));
  EXPECT_FALSE(DisableConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kSampled));

  // Every value-change / past function needs the clock named explicitly.
  for (SampledValueFunction fn :
       {SampledValueFunction::kRose, SampledValueFunction::kFell,
        SampledValueFunction::kStable, SampledValueFunction::kChanged,
        SampledValueFunction::kPast}) {
    EXPECT_TRUE(DisableConditionSampledValueRequiresExplicitClock(fn));
    EXPECT_FALSE(DisableConditionSampledValueClockIsWellFormed(
        fn, /*clock_explicitly_specified=*/false));
    EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(
        fn, /*clock_explicitly_specified=*/true));
  }
}

// §16.12 + §F.4.1: arity mismatch makes the flattened form not legal.
TEST(PropertyDeclarationElaboration, FlattenRejectsArgCountMismatch) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  decl.prop_formals = {"a", "b"};
  reg.Register(&decl);

  auto fp = reg.Flatten("p", 1);
  EXPECT_FALSE(fp.legal);
}

// §16.12 + §F.4.1: a well-formed flatten is acceptable as a top-level spec.
TEST(PropertyDeclarationElaboration, FlattenAcceptsWellFormedProperty) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  decl.prop_formals = {"x"};
  decl.prop_disable_iff_count = 1;
  reg.Register(&decl);

  auto fp = reg.Flatten("p", 1);
  EXPECT_TRUE(fp.legal);
  EXPECT_EQ(fp.disable_iff_count, 1);
  EXPECT_TRUE(PropertyRegistry::IsAcceptableAsTopLevelConcurrent(fp));
}

// §16.12: the dependency digraph of named properties has an edge for an
// instance in a formal's default actual, and one from a property to each
// property an instance of it names in an actual argument: q1 reaches q2
// through its default and q2 instantiates q1; r1 writes r2(r1), so r2
// reaches r1 and r1 instantiates r2.
TEST(PropertyDependencyGraph, DefaultsAndActualsAreEdges) {
  Expr q2_ref;
  q2_ref.kind = ExprKind::kIdentifier;
  q2_ref.text = "q2";
  ModuleItem q1;
  q1.kind = ModuleItemKind::kPropertyDecl;
  q1.name = "q1";
  q1.prop_formals = {"x"};
  q1.prop_formal_defaults = {&q2_ref};
  ModuleItem q2;
  q2.kind = ModuleItemKind::kPropertyDecl;
  q2.name = "q2";
  q2.prop_instance_refs = {"q1"};
  Expr r1_ref;
  r1_ref.kind = ExprKind::kIdentifier;
  r1_ref.text = "r1";
  Expr r2_call;
  r2_call.kind = ExprKind::kCall;
  r2_call.callee = "r2";
  r2_call.args = {&r1_ref};
  PropertyExprNode r1_body;
  r1_body.boolean = &r2_call;
  ModuleItem r1;
  r1.kind = ModuleItemKind::kPropertyDecl;
  r1.name = "r1";
  r1.prop_instance_refs = {"r2"};
  r1.prop_body_tree = &r1_body;
  ModuleItem r2;
  r2.kind = ModuleItemKind::kPropertyDecl;
  r2.name = "r2";
  PropertyRegistry reg;
  for (const ModuleItem* item : {&q1, &q2, &r1, &r2}) reg.Register(item);
  EXPECT_TRUE(reg.IsRecursiveProperty(&q1));
  EXPECT_TRUE(reg.IsRecursiveProperty(&q2));
  EXPECT_TRUE(reg.IsRecursiveProperty(&r1));
  EXPECT_TRUE(reg.IsRecursiveProperty(&r2));
}

// §16.12: a $ actual of a named property instance follows §16.8's rule: p1
// reads its untyped formal m as an operand.
TEST(PropertyDollarActual, AnOperandFormalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a, b;\n"
      "  property p1(m);\n"
      "    b == m;\n"
      "  endproperty\n"
      "  a1: assert property (@(posedge clk) a |-> p1($));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$ binds the formal 'm' of 'p1', which shall be "
                            "untyped",
                            6, "16.12"));
}

}  // namespace
