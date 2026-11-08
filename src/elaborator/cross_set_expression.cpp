#include "elaborator/cross_set_expression.h"

#include "elaborator/type_eval.h"

namespace delta {

bool CrossSetExpressionTypeAllowed(const DataType& cross_queue_type,
                                   const DataType& expr_type) {
  return IsAssignmentCompatible(cross_queue_type, expr_type);
}

bool CrossSetExpressionCastRequired(const DataType& cross_queue_type,
                                    const DataType& expr_type) {
  return !CrossSetExpressionTypeAllowed(cross_queue_type, expr_type);
}

}  // namespace delta
