#include "elaborator/function_in_checker.h"

namespace delta {

bool CheckerFunctionFreeVariableAllowed(
    CheckerFunctionFreeVariablePosition position) {
  switch (position) {
    case CheckerFunctionFreeVariablePosition::kFormalArgument:
    case CheckerFunctionFreeVariablePosition::kInternalVariable:
      // §17.8 forbids declaring a function's formals or internal variables as
      // free variables.
      return false;
    case CheckerFunctionFreeVariablePosition::kActualArgument:
      // §17.8 carves out the call site: a free variable may be passed in as an
      // actual argument.
      return true;
  }
  return false;
}

bool CheckerVariableAssignmentFunctionCallAllowed(FunctionArgKind arg_kind,
                                                  bool is_automatic,
                                                  bool preserves_no_state,
                                                  bool has_no_side_effects) {
  // §17.8 borrows §16.6's restrictions wholesale: the argument kinds permitted
  // and the automatic/stateless/no-side-effects eligibility are exactly those
  // applied to function calls in concurrent assertions.
  return FunctionArgKindAllowedInAssertionExpr(arg_kind) &&
         FunctionEligibleInAssertionExpr(is_automatic, preserves_no_state,
                                         has_no_side_effects);
}

}  // namespace delta
