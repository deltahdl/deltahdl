#pragma once

#include <cstdint>

namespace delta {

enum class PropertyFormalRuleAspect : uint8_t {
  kActualArgumentSubstitution,
  kAllowedTypeList,
  kTypedReferencePlacement,
};

bool PropertyFormalInheritsSequenceRule(PropertyFormalRuleAspect aspect);

enum class PropertyFormalTypeKind : uint8_t {
  kProperty,
  kSequence,
  kEvent,
  kAssertionExpressionType,
  kForbidden,
};

bool IsPropertyFormalTypeAllowed(PropertyFormalTypeKind kind);

enum class PropertyTypedFormalActualKind : uint8_t {
  kPropertyExpr,
  kBooleanExpression,
  kSequenceExpr,
  kNotAPropertyExpr,
};

bool IsPropertyTypedFormalActualLegal(PropertyTypedFormalActualKind kind);

enum class PropertyTypedFormalRefPlace : uint8_t {
  kPropertyExprPosition,
  kImplicationAntecedent,
  kOtherPosition,
};

bool IsPropertyTypedFormalRefLegal(PropertyTypedFormalRefPlace where);

}  // namespace delta
