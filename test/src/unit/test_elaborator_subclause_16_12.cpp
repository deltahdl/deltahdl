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

TEST(PropertyDeclarationElaboration, DisableConditionSampledValueNeedsClock) {
  EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, false));
  EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(
      SampledValueFunction::kSampled, true));
  EXPECT_FALSE(DisableConditionSampledValueRequiresExplicitClock(
      SampledValueFunction::kSampled));

  for (SampledValueFunction fn :
       {SampledValueFunction::kRose, SampledValueFunction::kFell,
        SampledValueFunction::kStable, SampledValueFunction::kChanged,
        SampledValueFunction::kPast}) {
    EXPECT_TRUE(DisableConditionSampledValueRequiresExplicitClock(fn));
    EXPECT_FALSE(DisableConditionSampledValueClockIsWellFormed(fn, false));
    EXPECT_TRUE(DisableConditionSampledValueClockIsWellFormed(fn, true));
  }
}

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

TEST(PropertyFlattening, AnInstanceWhoseFlattenedPropertyIsLegalIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p(x); @(posedge clk) x |-> b; endproperty\n"
      "  property q(x); @(posedge clk) a |-> x; endproperty\n"
      "  assert property (p(a ##1 b));\n"
      "  assert property (q(s_eventually b));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(PropertyFlattening, DISABLED_AnInstanceWhoseFlattenedPropertyIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p(x); @(posedge clk) x |-> b; endproperty\n"
      "  assert property (p(s_eventually a));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the flattened property of this instance of \"p\" is not legal", 4,
      "16.12"));
}

}  // namespace
