#pragma once

#include <cstdint>

namespace delta {

// §16.6: contexts where a Boolean expression appears inside a concurrent
// assertion. The same expression-content rules apply across all places; the
// runtime evaluation mode (sampled vs current values) differs by place and is
// modeled in the simulator.
enum class AssertionBooleanExprPlace : uint8_t {
  kSequenceOrPropertyExpr,
  kClockingEvent,
  kDisableCondition,
};

// §16.6: the overall expression result type must be cast compatible with an
// integral type. Subexpressions are exempt: only the top-level result is
// constrained.
bool ConcurrentAssertionExprTypeIsAcceptable(bool overall_result_castable);
bool ConcurrentAssertionSubexprTypeIsExempt();

// §16.6: a procedural concurrent assertion may reference automatic variables
// (per §16.14.6.1); any non-procedural concurrent assertion may not.
bool AutomaticVariableReferenceAllowed(
    bool inside_procedural_concurrent_assertion);

// §16.6: expressions shall not reference non-static class properties or
// methods.
bool NonStaticClassMemberReferenceAllowed();

// §16.6: expressions shall not reference variables of chandle type.
bool ChandleVariableReferenceAllowed();

// §16.6: a sequence_match_item with a local variable as the variable_lvalue
// may use C assignment / increment / decrement. Outside that one exception,
// evaluating a Boolean expression in a concurrent assertion shall have no
// side effects.
bool SideEffectAllowed(bool inside_sequence_match_item,
                       bool variable_lvalue_is_local);

// §16.6: a function called from a concurrent-assertion Boolean expression
// shall not declare output, inout, or ref formal arguments; const ref is
// permitted.
enum class FunctionArgKind : uint8_t {
  kInput,
  kOutput,
  kInout,
  kRef,
  kConstRef,
};
bool FunctionArgKindAllowedInAssertionExpr(FunctionArgKind kind);

// §16.6: a function used in a concurrent-assertion expression must be
// automatic (or stateless: "preserve no state information") and have no side
// effects.
bool FunctionEligibleInAssertionExpr(bool is_automatic, bool preserves_no_state,
                                     bool has_no_side_effects);

// §16.6: a disable-condition expression may reference the sequence method
// `triggered` but shall not reference local variables or the sequence method
// `matched`. Other (non-local, non-matched) references are unrestricted by
// this rule.
enum class DisableConditionRefKind : uint8_t {
  kOrdinaryVariable,
  kLocalVariable,
  kTriggeredMethod,
  kMatchedMethod,
};
bool DisableConditionRefAllowed(DisableConditionRefKind kind);

}  // namespace delta
