#pragma once

#include <cstdint>

namespace delta {

// Semantic rules for the let construct (§11.12). A let declaration defines a
// template expression that is expanded into the places where it is
// instantiated. The grammar of let_declaration is borrowed from A.2.12; the
// rules encoded here are the ones stated in the prose of §11.12 itself, and
// they apply at elaboration time. Each helper is a pure classifier so the
// canonical elaborator test can exercise the rule directly.

// §11.12: a let formal argument may optionally be typed. If it is typed, then
// the type shall be `event` or one of the types allowed in §16.6. Unlike a
// sequence formal (§16.8.1) or a property formal (§16.12.18), a let formal
// admits neither `sequence` nor `property`; the only choices beyond `untyped`
// are `event` and the §16.6 type list.
enum class LetFormalTypeKind : uint8_t {
  kUntyped,            // the `untyped` keyword — the formal is not typed
  kEvent,              // event
  kTypeAllowedIn16_6,  // one of the types allowed in §16.6
  kForbidden,          // anything else (e.g. sequence, property)
};

bool IsLetFormalTypeAllowed(LetFormalTypeKind kind);

// §11.12, rule 1: if the formal is of type `event`, the corresponding actual
// argument shall be an event_expression.
bool IsLetEventFormalActualLegal(bool actual_is_event_expression);

// §11.12, rule 1: each reference to an `event`-typed formal shall be in a
// place where an event_expression may be written.
bool IsLetEventTypedFormalRefLegal(bool in_event_expression_position);

// §11.12, rule 2: for a typed formal that is not of type `event`, the
// self-determined result type of the actual argument shall be cast compatible
// (see §6.22.4) with the type of the formal argument.
bool IsLetNonEventFormalActualLegal(bool self_determined_type_cast_compatible);

// §11.12: rule 1 substitutes an event formal as an event_expression, whereas
// rule 2 casts the actual to the formal's type before it is substituted for a
// reference to the formal in the rewriting algorithm (see §F.4).
enum class LetTypedFormalSubstitutionMode : uint8_t {
  kEventExpressionSubstitution,  // event formal — substituted, no cast
  kCastBeforeSubstitution,       // non-event typed formal — cast to the type
};

LetTypedFormalSubstitutionMode LetTypedFormalSubstitution(bool formal_is_event);

// §11.12: variables used in a let body that are not formal arguments are
// resolved in the scope where the let is declared. In that scope, a let body
// shall be defined before it is used; a use that precedes the declaration is
// illegal.
bool IsLetUseAfterDeclarationLegal(bool declared_before_use);

// §11.12: no hierarchical references to let declarations are allowed. A let
// may be instantiated by a simple (optionally package-scoped) name, but never
// reached through a hierarchical path.
bool IsLetReferenceLegal(bool is_hierarchical_reference);

// §11.12: a let body may contain sampled value function calls (§16.9.3,
// §16.9.4). When such a call has no explicit clock, its clock is inferred in
// the instantiation context exactly as if the function were used directly
// there. It shall be an error if a clock is required but cannot be inferred in
// the instantiation context.
enum class LetSampledValueClockStatus : uint8_t {
  kExplicit,                  // the sampled value call names its own clock
  kInferredFromContext,       // no explicit clock, but one is inferable
  kRequiredButNotInferable,   // a clock is required yet none can be inferred
};

bool IsLetSampledValueClockResolved(LetSampledValueClockStatus status);

}  // namespace delta
