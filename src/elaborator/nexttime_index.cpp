#include "elaborator/nexttime_index.h"

namespace delta {

NexttimeIndex MakeNexttimeIndex(long long value) {
  NexttimeIndex index;
  index.is_constant = true;
  index.is_integer = true;
  index.value = value;
  return index;
}

bool IsNexttimeIndexWellFormed(const NexttimeIndex& index) {
  // §16.12.10: the number of clock ticks shall be a non-negative integer
  // constant expression. An index that does not fold to a constant, or that
  // folds to a non-integer constant, is rejected; a constant integer index is
  // accepted only when its value is not negative.
  if (!index.is_constant) return false;
  if (!index.is_integer) return false;
  return index.value >= 0;
}

}  // namespace delta
