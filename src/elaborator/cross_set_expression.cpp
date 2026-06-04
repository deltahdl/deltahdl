#include "elaborator/cross_set_expression.h"

#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

bool CrossSetExpressionTypeAllowed(const DataType& cross_queue_type,
                                   const DataType& expr_type) {
  // §19.6.1.4: the expression may be used as written only when it evaluates to
  // the cross's CrossQueueType — that is, when its type is assignment compatible
  // with the cross queue type, the target the cross supplies as context.
  return IsAssignmentCompatible(cross_queue_type, expr_type);
}

bool CrossSetExpressionCastRequired(const DataType& cross_queue_type,
                                    const DataType& expr_type) {
  // §19.6.1.4: a cast is required precisely when the expression's type is
  // assignment-incompatible with the cross type.
  return !CrossSetExpressionTypeAllowed(cross_queue_type, expr_type);
}

}  // namespace delta
