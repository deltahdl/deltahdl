#pragma once

#include <cstdint>

namespace delta {

// §16.12.18: the §16.8.1 rules for typed formal arguments and their actual
// arguments apply to named properties, except as described next. This enum
// names the rule aspects so callers can tell which §16.8.1 behavior carries
// over unchanged and which is overridden by §16.12.18.
enum class PropertyFormalRuleAspect : uint8_t {
  kActualArgumentSubstitution,  // inherited from §16.8.1 unchanged
  kAllowedTypeList,             // overridden: §16.12.18 adds `property`
  kTypedReferencePlacement,     // overridden: property-type reference rules
};

bool PropertyFormalInheritsSequenceRule(PropertyFormalRuleAspect aspect);

// §16.12.18: if a formal argument of a named property is typed, then the
// type shall be `property`, `sequence`, `event`, or one of the types allowed
// in §16.6. The presence of `property` is what sets this list apart from the
// §16.8.1 sequence list.
enum class PropertyFormalTypeKind : uint8_t {
  kProperty,
  kSequence,
  kEvent,
  kTypeAllowedIn166,
  kForbidden,
};

bool IsPropertyFormalTypeAllowed(PropertyFormalTypeKind kind);

// §16.12.18: if the formal argument is of type `property`, the corresponding
// actual argument shall be a property_expr. A Boolean expression and a
// sequence_expr each satisfy this, because each is itself a property_expr;
// anything that is not a property_expr does not.
enum class PropertyTypedFormalActualKind : uint8_t {
  kPropertyExpr,
  kBooleanExpression,
  kSequenceExpr,
  kNotAPropertyExpr,
};

bool IsPropertyTypedFormalActualLegal(PropertyTypedFormalActualKind kind);

// §16.12.18: each reference to a `property`-typed formal shall be in a place
// where a property_expr may be written. A reference standing as the
// antecedent of `|->` or `|=>` (see §16.12.7) is illegal regardless of the
// actual argument, because a property_expr may not be written in that
// position.
enum class PropertyTypedFormalRefPlace : uint8_t {
  kPropertyExprPosition,
  kImplicationAntecedent,
  kOtherPosition,
};

bool IsPropertyTypedFormalRefLegal(PropertyTypedFormalRefPlace where);

}  // namespace delta
