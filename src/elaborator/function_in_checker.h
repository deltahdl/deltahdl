#pragma once

#include <cstdint>

#include "elaborator/concurrent_assertion_expr.h"

namespace delta {

// §17.8: a free variable must not appear in certain positions relative to a
// function that is used inside a checker. The formal arguments and the internal
// (local) variables of such a function shall not be declared as free variables;
// a free variable may, however, be passed in as an actual argument at the call
// site.
enum class CheckerFunctionFreeVariablePosition : uint8_t {
  kFormalArgument,    // a formal argument declared by the function
  kInternalVariable,  // an internal/local variable declared by the function
  kActualArgument,    // an actual argument supplied at the call site
};
bool CheckerFunctionFreeVariableAllowed(
    CheckerFunctionFreeVariablePosition position);

// §17.8: an expression on the right-hand side of a checker variable assignment
// may include a function call, but the call is legal only when it meets the
// same restrictions §16.6 imposes on function calls within concurrent
// assertions. Those restrictions are owned by §16.6; this entry point reuses
// that machinery so the checker-variable-assignment context is held to the same
// bar.
bool CheckerVariableAssignmentFunctionCallAllowed(FunctionArgKind arg_kind,
                                                  bool is_automatic,
                                                  bool preserves_no_state,
                                                  bool has_no_side_effects);

}  // namespace delta
