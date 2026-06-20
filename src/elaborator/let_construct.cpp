#include "elaborator/let_construct.h"

namespace delta {

bool IsLetFormalTypeAllowed(LetFormalTypeKind kind) {
  switch (kind) {
    case LetFormalTypeKind::kUntyped:
    case LetFormalTypeKind::kEvent:
    case LetFormalTypeKind::kTypeAllowedIn16_6:
      return true;
    case LetFormalTypeKind::kForbidden:
      return false;
  }
  return false;
}

bool IsLetEventFormalActualLegal(bool actual_is_event_expression) {
  // §11.12, rule 1: an event-typed formal accepts only an event_expression
  // actual.
  return actual_is_event_expression;
}

bool IsLetEventTypedFormalRefLegal(bool in_event_expression_position) {
  // §11.12, rule 1: a reference to an event-typed formal is legal only where
  // an event_expression may be written.
  return in_event_expression_position;
}

bool IsLetNonEventFormalActualLegal(bool self_determined_type_cast_compatible) {
  // §11.12, rule 2: the actual's self-determined result type must be cast
  // compatible (§6.22.4) with the non-event formal's type.
  return self_determined_type_cast_compatible;
}

LetTypedFormalSubstitutionMode LetTypedFormalSubstitution(
    bool formal_is_event) {
  // §11.12: an event formal is substituted as an event_expression; any other
  // typed formal has its actual cast to the formal's type before the actual
  // is spliced in by the rewriting algorithm (§F.4).
  return formal_is_event
             ? LetTypedFormalSubstitutionMode::kEventExpressionSubstitution
             : LetTypedFormalSubstitutionMode::kCastBeforeSubstitution;
}

bool IsLetUseAfterDeclarationLegal(bool declared_before_use) {
  // §11.12: within the declaring scope, the let body must already be defined
  // at the point of use.
  return declared_before_use;
}

bool IsLetReferenceLegal(bool is_hierarchical_reference) {
  // §11.12: a hierarchical reference can never reach a let declaration.
  return !is_hierarchical_reference;
}

bool IsLetSampledValueClockResolved(LetSampledValueClockStatus status) {
  switch (status) {
    case LetSampledValueClockStatus::kExplicit:
    case LetSampledValueClockStatus::kInferredFromContext:
      return true;
    case LetSampledValueClockStatus::kRequiredButNotInferable:
      // §11.12: a required-but-uninferable clock in the instantiation context
      // is an error.
      return false;
  }
  return false;
}

}  // namespace delta
