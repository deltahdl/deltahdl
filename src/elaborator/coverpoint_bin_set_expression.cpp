#include "elaborator/coverpoint_bin_set_expression.h"

#include "elaborator/type_eval.h"

namespace delta {

bool SetExpressionElementTypeAllowed(const DataType& coverpoint_type,
                                     const DataType& element_type) {
  return IsAssignmentCompatible(coverpoint_type, element_type);
}

bool SetExpressionArrayKindAllowed(SetExpressionArrayKind kind) {
  return kind != SetExpressionArrayKind::kAssociative;
}

bool SetExpressionNameVisible(SetExpressionNameOrigin origin) {
  return origin == SetExpressionNameOrigin::kExternal;
}

}  // namespace delta
