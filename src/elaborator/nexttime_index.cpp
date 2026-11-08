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
  if (!index.is_constant) return false;
  if (!index.is_integer) return false;
  return index.value >= 0;
}

}  // namespace delta
