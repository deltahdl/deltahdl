#ifndef DELTA_ELABORATOR_CROSS_SET_EXPRESSION_H
#define DELTA_ELABORATOR_CROSS_SET_EXPRESSION_H

namespace delta {

struct DataType;

// §19.6.1.4 "Cross bin set expression". A cross_set_expression names an
// expression that yields a queue of elements defining a cross bin, the cross
// analog of the set_covergroup_expression that defines a coverpoint bin (see the
// §19.5.1.2 helpers). The cross_set_expression production itself belongs to
// §19.6.1's Syntax 19-4 (and the matches selection policy is the same one
// §19.6.1.2 defines; see CrossWithMatchPolicy / SelectCrossBinTuples in the
// simulator). The rule that §19.6.1.4 adds on its own is a type rule: the queue
// the expression evaluates to shall be the cross's CrossQueueType, whose
// elements are of type CrossValType (see §19.6.1.3). The cross supplies the
// context type, so a bare literal array is not required — any expression is
// permitted as long as it evaluates to the cross's CrossQueueType, and a cast is
// required when the expression's type is assignment-incompatible with it. The
// helpers below carry that compile-time type rule for the elaborator.

// §19.6.1.4: the cross bin provides the context type — the cross's
// CrossQueueType — into which the cross_set_expression's value is effectively
// assigned. Returns true when the expression's type may be used as written, i.e.
// it is assignment compatible with the cross's CrossQueueType, reusing the
// §6.22.1 assignment-compatibility rule. cross_queue_type is the assignment
// target.
bool CrossSetExpressionTypeAllowed(const DataType& cross_queue_type,
                                   const DataType& expr_type);

// §19.6.1.4: a cast is required if the expression's type is
// assignment-incompatible with the cross type. Returns true exactly when the
// expression cannot be used as written and an explicit cast to the cross's
// CrossQueueType is required — the complement of CrossSetExpressionTypeAllowed.
bool CrossSetExpressionCastRequired(const DataType& cross_queue_type,
                                    const DataType& expr_type);

}  // namespace delta

#endif  // DELTA_ELABORATOR_CROSS_SET_EXPRESSION_H
