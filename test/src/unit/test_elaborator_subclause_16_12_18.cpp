#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "elaborator/typed_property_formal.h"
#include "fixture_elaborator.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

// The process the module's one static concurrent assertion is lowered to.
const RtlirProcess* TheAssertionProcess(const RtlirModule* mod) {
  for (const auto& p : mod->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysFF) return &p;
  }
  return nullptr;
}

// §16.12.18 by way of §16.8.1: an instance whose actual for a formal of
// type event is an event expression is evaluated on that event, the edge
// and the signal the actual names in the clock's place.
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
  // §16.12.18: the §16.8.1 typed-formal rules apply to named properties,
  // except as described next. The actual-argument substitution machinery is
  // inherited unchanged; the allowed-type list and the typed-reference
  // placement rules are overridden by §16.12.18.
  EXPECT_TRUE(PropertyFormalInheritsSequenceRule(
      PropertyFormalRuleAspect::kActualArgumentSubstitution));
  EXPECT_FALSE(PropertyFormalInheritsSequenceRule(
      PropertyFormalRuleAspect::kAllowedTypeList));
  EXPECT_FALSE(PropertyFormalInheritsSequenceRule(
      PropertyFormalRuleAspect::kTypedReferencePlacement));
}

TEST(TypedPropertyFormal,
     AllowedTypeKindsIncludePropertySequenceEventOrDataType) {
  // §16.12.18: a typed formal of a named property shall be `property`,
  // `sequence`, `event`, or one of the types allowed in §16.6. The addition
  // of `property` is what distinguishes this list from the §16.8.1 one.
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kProperty));
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kSequence));
  EXPECT_TRUE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kEvent));
  EXPECT_TRUE(
      IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kTypeAllowedIn166));
}

TEST(TypedPropertyFormal, ForbiddenTypeKindRejected) {
  // §16.12.18: a type outside the allowed list is not a valid property
  // formal type.
  EXPECT_FALSE(IsPropertyFormalTypeAllowed(PropertyFormalTypeKind::kForbidden));
}

TEST(TypedPropertyFormal, PropertyTypedActualMustBePropertyExpr) {
  // §16.12.18: if the formal is of type `property`, the corresponding actual
  // argument shall be a property_expr. A Boolean expression and a
  // sequence_expr each qualify because each is itself a property_expr.
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
  // §16.12.18: each reference to a `property`-typed formal shall be in a
  // place where a property_expr may be written. A reference standing as the
  // antecedent of |-> or |=> (see §16.12.7) is illegal regardless of the
  // actual argument, because a property_expr may not be written there.
  EXPECT_TRUE(IsPropertyTypedFormalRefLegal(
      PropertyTypedFormalRefPlace::kPropertyExprPosition));
  EXPECT_FALSE(IsPropertyTypedFormalRefLegal(
      PropertyTypedFormalRefPlace::kImplicationAntecedent));
  EXPECT_FALSE(IsPropertyTypedFormalRefLegal(
      PropertyTypedFormalRefPlace::kOtherPosition));
}

}  // namespace
