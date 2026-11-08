#pragma once

namespace delta {

struct NexttimeIndex {
  bool is_constant = false;
  bool is_integer = false;
  long long value = 0;
};

NexttimeIndex MakeNexttimeIndex(long long value);

bool IsNexttimeIndexWellFormed(const NexttimeIndex& index);

}  // namespace delta
