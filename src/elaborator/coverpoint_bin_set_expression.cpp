#include "elaborator/coverpoint_bin_set_expression.h"

#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

bool SetExpressionElementTypeAllowed(const DataType& coverpoint_type,
                                     const DataType& element_type) {
  // §19.5.1.2: the array's element type must be assignment compatible with the
  // coverpoint type, into which its values are effectively assigned.
  return IsAssignmentCompatible(coverpoint_type, element_type);
}

bool SetExpressionArrayKindAllowed(SetExpressionArrayKind kind) {
  // §19.5.1.2: every array kind is permitted except an associative array.
  return kind != SetExpressionArrayKind::kAssociative;
}

bool SetExpressionNameVisible(SetExpressionNameOrigin origin) {
  // §19.5.1.2: coverpoint identifiers and bin identifiers declared within the
  // covergroup are not visible; only a name declared outside it can be seen.
  return origin == SetExpressionNameOrigin::kExternal;
}

}  // namespace delta
