#pragma once

#include <algorithm>
#include <cstdint>

namespace delta {

struct PackedRange {
  int64_t left = 0;
  int64_t right = 0;

  static PackedRange Implicit(uint32_t width) {
    return {width == 0 ? 0 : static_cast<int64_t>(width) - 1, 0};
  }

  int64_t LowIndex() const { return std::min(left, right); }
  int64_t HighIndex() const { return std::max(left, right); }

  bool Contains(int64_t idx) const {
    return idx >= LowIndex() && idx <= HighIndex();
  }

  int64_t Clamp(int64_t idx) const {
    return std::clamp(idx, LowIndex(), HighIndex());
  }

  int64_t OffsetOf(int64_t idx) const {
    return (left >= right) ? idx - right : right - idx;
  }

  int64_t IndexAtOffset(int64_t offset) const {
    return (left >= right) ? right + offset : right - offset;
  }

  int64_t PlusSelectBase(int64_t offset, int64_t width) const {
    return (left >= right) ? right + offset : right - offset - width + 1;
  }
};

struct PartSelectIndices {
  int64_t first = 0;
  int64_t second = 0;
  int64_t declared_width = 1;
};

struct PartSelectBits {
  uint32_t lo = 0;
  uint32_t width = 0;
  uint32_t src_lo = 0;
};

inline PartSelectIndices PartSelectTargetIndices(int64_t idx, int64_t end_val,
                                                 bool is_plus, bool is_minus) {
  if (is_plus) return {idx, idx + end_val - 1, end_val};
  if (is_minus) return {idx - end_val + 1, idx, end_val};
  return {idx, end_val, 1};
}

inline PartSelectBits PartSelectStorageBits(const PackedRange& range,
                                            int64_t first, int64_t second) {
  int64_t lo_idx = std::min(first, second);
  int64_t hi_idx = std::max(first, second);
  if (hi_idx < range.LowIndex() || lo_idx > range.HighIndex()) return {0, 0, 0};
  auto a = static_cast<uint32_t>(range.OffsetOf(range.Clamp(lo_idx)));
  auto b = static_cast<uint32_t>(range.OffsetOf(range.Clamp(hi_idx)));
  uint32_t lo = std::min(a, b);
  int64_t below = std::min(range.OffsetOf(lo_idx), range.OffsetOf(hi_idx));
  return {lo, std::max(a, b) - lo + 1,
          below < 0 ? static_cast<uint32_t>(-below) : 0};
}

}  // namespace delta
