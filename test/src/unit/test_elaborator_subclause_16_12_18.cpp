#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "elaborator/typed_property_formal.h"
#include "fixture_elaborator.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

const RtlirProcess* TheAssertionProcess(const RtlirModule* mod) {
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) return &p;
  }
  return nullptr;
}

TEST(TypedPropertyFormal, AnEventActualSuppliesTheInstancesClock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  property p_ev(event ev);\n"
      "    @(ev) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p_ev(negedge clk));\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirProcess* p = TheAssertionProcess(design->top_modules[0]);
  ASSERT_NE(p, nullptr);
  ASSERT_EQ(p->sensitivity.size(), 1u);
  EXPECT_EQ(p->sensitivity[0].edge, Edge::kNegedge);
  ASSERT_NE(p->sensitivity[0].signal, nullptr);
  EXPECT_EQ(p->sensitivity[0].signal->text, "clk");
}

TEST(TypedPropertyFormal, SequenceRulesCarryOverExceptOverriddenAspects) {
  EXPECT_TRUE(PropertyFormalInheritsSequenceRule(
      PropertyFormalRuleAspect::kActualArgumentSubstitution));
  EXPECT_FALSE(PropertyFormalInheritsSequenceRule(
      PropertyFormalRuleAspect::kAllowedTypeList));
  EXPECT_FALSE(PropertyFormalInheritsSequenceRule(
      PropertyFormalRuleAspect::kTypedReferencePlacement));
}

TEST(TypedPropertyFormal,
     AllowedTypeKindsIncludePropertySequenceEventOrDataType) {
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kProperty));
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kSequence));
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kEvent));
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(
      PropertyFormalTypeKind::kAssertionExpressionType));
}

TEST(TypedPropertyFormal, ForbiddenTypeKindRejected) {
  EXPECT_FALSE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kForbidden));
}

TEST(TypedPropertyFormal, PropertyTypedActualMustBePropertyExpr) {
  EXPECT_TRUE(IsPropertyTypedFormalActualLegal(
      PropertyTypedFormalActualKind::kPropertyExpr));
  EXPECT_TRUE(IsPropertyTypedFormalActualLegal(
      PropertyTypedFormalActualKind::kBooleanExpression));
  EXPECT_TRUE(IsPropertyTypedFormalActualLegal(
      PropertyTypedFormalActualKind::kSequenceExpr));
  EXPECT_FALSE(IsPropertyTypedFormalActualLegal(
      PropertyTypedFormalActualKind::kNotAPropertyExpr));
}

TEST(TypedPropertyFormal, PropertyTypedRefLegalOnlyWherePropertyExprAllowed) {
  EXPECT_TRUE(IsPropertyTypedFormalRefLegal(
      PropertyTypedFormalRefPlace::kPropertyExprPosition));
  EXPECT_FALSE(IsPropertyTypedFormalRefLegal(
      PropertyTypedFormalRefPlace::kImplicationAntecedent));
  EXPECT_FALSE(IsPropertyTypedFormalRefLegal(
      PropertyTypedFormalRefPlace::kOtherPosition));
}

TEST(TypedPropertyFormal, ATreeActualGivesABooleanBodysInstanceATree) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, b, c;\n"
      "  property p_not(property q);\n"
      "    @(posedge clk) not q;\n"
      "  endproperty\n"
      "  assert property (p_not(b |-> c));\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirProcess* p = TheAssertionProcess(design->top_modules[0]);
  ASSERT_NE(p, nullptr);
  ASSERT_NE(p->body, nullptr);
  EXPECT_FALSE(p->body->assert_negated);
  const PropertyExprNode* root = p->body->assert_property;
  ASSERT_NE(root, nullptr);
  EXPECT_EQ(root->kind, PropertyExprNode::Kind::kBoolean);
  ASSERT_NE(root->boolean, nullptr);
  EXPECT_EQ(root->boolean->kind, ExprKind::kCall);
  ASSERT_EQ(root->boolean->args.size(), 1u);
  const PropertyExprNode* actual = root->boolean->args[0]->property_actual;
  ASSERT_NE(actual, nullptr);
  EXPECT_EQ(actual->kind, PropertyExprNode::Kind::kImplication);
}

}  // namespace
