#include "elaborator/function_in_checker.h"

#include "elaborator/concurrent_assertion_expr.h"

namespace delta {

bool CheckerFunctionFreeVariableAllowed(
    CheckerFunctionFreeVariablePosition position) {
  switch (position) {
    case CheckerFunctionFreeVariablePosition::kFormalArgument:
    case CheckerFunctionFreeVariablePosition::kInternalVariable:
      return false;
    case CheckerFunctionFreeVariablePosition::kActualArgument:
      return true;
  }
  return false;
}

bool CheckerVariableAssignmentFunctionCallAllowed(FunctionArgKind arg_kind,
                                                  bool is_automatic,
                                                  bool preserves_no_state,
                                                  bool has_no_side_effects) {
  return FunctionArgKindAllowedInAssertionExpr(arg_kind) &&
         FunctionEligibleInAssertionExpr(is_automatic, preserves_no_state,
                                         has_no_side_effects);
}

}  // namespace delta
