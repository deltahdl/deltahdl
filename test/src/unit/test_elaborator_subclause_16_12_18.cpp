#include <gtest/gtest.h>

#include "elaborator/typed_property_formal.h"

using namespace delta;

namespace {

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
