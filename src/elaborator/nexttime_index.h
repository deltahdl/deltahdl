#pragma once

#include <cstdint>

namespace delta {

// §16.12.10: the indexed nexttime property forms
// `nexttime [constant_expression] property_expr` and
// `s_nexttime [constant_expression] property_expr` take a bracketed index that
// gives a number of clock ticks. That number shall be a non-negative integer
// constant expression. This records the three facts the elaborator must
// establish about the index expression: that it folds to a compile-time
// constant, that the folded constant is an integer, and that the integer is not
// negative.
struct NexttimeIndex {
  bool is_constant = false;
  bool is_integer = false;
  long long value = 0;
};

// §16.12.10: build an index from an already-folded non-negative integer
// constant. The result is well-formed by construction.
NexttimeIndex MakeNexttimeIndex(long long value);

// §16.12.10: the number of clock ticks shall be a non-negative integer constant
// expression. All three conditions must hold: the index folds to a constant,
// the constant is an integer, and the integer value is not negative.
bool IsNexttimeIndexWellFormed(const NexttimeIndex& index);

}  // namespace delta
