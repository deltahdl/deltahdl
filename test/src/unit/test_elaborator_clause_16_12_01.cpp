#include <gtest/gtest.h>

#include "elaborator/property_instantiation.h"

using namespace delta;

namespace {

TEST(PropertyInstantiation, LegalAsPropertyExprWhenBodyFits) {
  // §16.12.1: an instance is legal as a property_expr provided the named
  // property's body — with actuals substituted for formals — is itself a
  // legal property_expr.
  EXPECT_TRUE(
      IsPropertyInstanceLegal(PropertyInstancePlacement::kAsPropertyExpr,
                              /*body_substitutable_at_placement=*/true));
}

TEST(PropertyInstantiation, LegalAsPropertySpecWhenBodyFits) {
  // §16.12.1: the same legality test applies when the instance is used as a
  // property_spec rather than a property_expr.
  EXPECT_TRUE(
      IsPropertyInstanceLegal(PropertyInstancePlacement::kAsPropertySpec,
                              /*body_substitutable_at_placement=*/true));
}

TEST(PropertyInstantiation, RejectedWhenSubstitutionWouldBeIllegal) {
  // §16.12.1: if substituting actuals would not yield a legal property at
  // the placement, the instance is not legal.
  EXPECT_FALSE(
      IsPropertyInstanceLegal(PropertyInstancePlacement::kAsPropertyExpr,
                              /*body_substitutable_at_placement=*/false));
}

TEST(PropertyInstantiation, BuildingOperatorOperandRejectsDisableIff) {
  // §16.12.1: if an instance of a named property is used as a property_expr
  // operand of any property-building operator, the named property may not
  // have a disable iff clause.
  EXPECT_FALSE(IsPropertyInstanceLegalAsBuildingOperatorOperand(
      /*named_property_has_disable_iff=*/true));
  EXPECT_TRUE(IsPropertyInstanceLegalAsBuildingOperatorOperand(
      /*named_property_has_disable_iff=*/false));
}

}  // namespace
