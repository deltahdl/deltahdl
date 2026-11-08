#pragma once

#include <cstdint>

#include "elaborator/concurrent_assertion_expr.h"

namespace delta {

enum class CheckerFunctionFreeVariablePosition : uint8_t {
  kFormalArgument,
  kInternalVariable,
  kActualArgument,
};
bool CheckerFunctionFreeVariableAllowed(
    CheckerFunctionFreeVariablePosition position);

bool CheckerVariableAssignmentFunctionCallAllowed(FunctionArgKind arg_kind,
                                                  bool is_automatic,
                                                  bool preserves_no_state,
                                                  bool has_no_side_effects);

}  // namespace delta
