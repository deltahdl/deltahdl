#pragma once

#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;

class AssocIndex {
 public:
  AssocIndex() = default;
  AssocIndex(int64_t value);

  static AssocIndex Of(const Logic4Vec& val, bool is_wildcard,
                       uint32_t index_width, bool is_signed);

  Logic4Vec ToVec(Arena& arena, uint32_t width, bool is_signed) const;

  int64_t Low() const { return low_; }

  Logic4Vec ToSignedVec(Arena& arena) const;

  friend bool operator<(const AssocIndex& a, const AssocIndex& b);
  friend bool operator==(const AssocIndex& a, const AssocIndex& b) {
    return a.low_ == b.low_ && a.high_ == b.high_;
  }

 private:
  int64_t low_ = 0;
  std::vector<uint64_t> high_;

  void Trim();
  bool IsNegative() const;
  uint64_t Word(size_t i) const;
  size_t WordCount() const { return high_.size() + 1; }
};

}  // namespace delta
