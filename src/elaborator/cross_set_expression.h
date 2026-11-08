#ifndef DELTA_ELABORATOR_CROSS_SET_EXPRESSION_H
#define DELTA_ELABORATOR_CROSS_SET_EXPRESSION_H

namespace delta {

struct DataType;

bool CrossSetExpressionTypeAllowed(const DataType& cross_queue_type,
                                   const DataType& expr_type);

bool CrossSetExpressionCastRequired(const DataType& cross_queue_type,
                                    const DataType& expr_type);

}  // namespace delta

#endif
