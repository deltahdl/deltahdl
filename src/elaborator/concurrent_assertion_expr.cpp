#include "elaborator/concurrent_assertion_expr.h"

namespace delta {

bool ConcurrentAssertionExprTypeIsAcceptable(bool overall_result_castable) {
  return overall_result_castable;
}

bool ConcurrentAssertionSubexprTypeIsExempt() {
  // §16.6 carves out subexpressions explicitly: only the overall expression
  // must be cast compatible with an integral type.
  return true;
}

bool AutomaticVariableReferenceAllowed(
    bool inside_procedural_concurrent_assertion) {
  return inside_procedural_concurrent_assertion;
}

bool NonStaticClassMemberReferenceAllowed() { return false; }

bool ChandleVariableReferenceAllowed() { return false; }

bool SideEffectAllowed(bool inside_sequence_match_item,
                       bool variable_lvalue_is_local) {
  return inside_sequence_match_item && variable_lvalue_is_local;
}

bool FunctionArgKindAllowedInAssertionExpr(FunctionArgKind kind) {
  switch (kind) {
    case FunctionArgKind::kInput:
    case FunctionArgKind::kConstRef:
      return true;
    case FunctionArgKind::kOutput:
    case FunctionArgKind::kInout:
    case FunctionArgKind::kRef:
      return false;
  }
  return false;
}

bool FunctionEligibleInAssertionExpr(bool is_automatic, bool preserves_no_state,
                                     bool has_no_side_effects) {
  // §16.6 phrases the lifetime constraint as automatic OR stateless: a static
  // function with no preserved state is acceptable in lieu of an automatic
  // one. The no-side-effects requirement is independent and always required.
  return (is_automatic || preserves_no_state) && has_no_side_effects;
}

bool DisableConditionRefAllowed(DisableConditionRefKind kind) {
  switch (kind) {
    case DisableConditionRefKind::kOrdinaryVariable:
    case DisableConditionRefKind::kTriggeredMethod:
      return true;
    case DisableConditionRefKind::kLocalVariable:
    case DisableConditionRefKind::kMatchedMethod:
      return false;
  }
  return false;
}

}  // namespace delta
