#include "elaborator/typed_property_formal.h"

namespace delta {

bool PropertyFormalInheritsSequenceRule(PropertyFormalRuleAspect aspect) {
  // §16.12.18: "apply ... except as described next." The substitution of
  // actual arguments follows §16.8.1 verbatim; the allowed-type list and the
  // typed-reference placement rules are the carve-outs spelled out here.
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
    case PropertyFormalTypeKind::kTypeAllowedIn166:
      return true;
    case PropertyFormalTypeKind::kForbidden:
      return false;
  }
  return false;
}

bool IsPropertyTypedFormalActualLegal(PropertyTypedFormalActualKind kind) {
  // §16.12.18: the actual for a `property`-typed formal must be a
  // property_expr. A Boolean expression and a sequence_expr are admitted
  // precisely because each is a property_expr.
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
  // §16.12.18: a reference to a `property`-typed formal is legal only where a
  // property_expr may be written. The antecedent of an overlapping or
  // non-overlapping implication (§16.12.7) is not such a place, so a
  // reference there is illegal regardless of the actual argument.
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
