#include "elaborator/typed_property_formal.h"

namespace delta {

bool PropertyFormalInheritsSequenceRule(PropertyFormalRuleAspect aspect) {
  switch (aspect) {
    case PropertyFormalRuleAspect::kActualArgumentSubstitution:
      return true;
    case PropertyFormalRuleAspect::kAllowedTypeList:
    case PropertyFormalRuleAspect::kTypedReferencePlacement:
      return false;
  }
  return false;
}

bool IsPropertyFormalTypeAllowed(PropertyFormalTypeKind kind) {
  switch (kind) {
    case PropertyFormalTypeKind::kProperty:
    case PropertyFormalTypeKind::kSequence:
    case PropertyFormalTypeKind::kEvent:
    case PropertyFormalTypeKind::kAssertionExpressionType:
      return true;
    case PropertyFormalTypeKind::kForbidden:
      return false;
  }
  return false;
}

bool IsPropertyTypedFormalActualLegal(PropertyTypedFormalActualKind kind) {
  switch (kind) {
    case PropertyTypedFormalActualKind::kPropertyExpr:
    case PropertyTypedFormalActualKind::kBooleanExpression:
    case PropertyTypedFormalActualKind::kSequenceExpr:
      return true;
    case PropertyTypedFormalActualKind::kNotAPropertyExpr:
      return false;
  }
  return false;
}

bool IsPropertyTypedFormalRefLegal(PropertyTypedFormalRefPlace where) {
  switch (where) {
    case PropertyTypedFormalRefPlace::kPropertyExprPosition:
      return true;
    case PropertyTypedFormalRefPlace::kImplicationAntecedent:
    case PropertyTypedFormalRefPlace::kOtherPosition:
      return false;
  }
  return false;
}

}  // namespace delta
