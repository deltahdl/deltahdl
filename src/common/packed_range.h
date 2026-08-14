#pragma once

#include <algorithm>
#include <cstdint>

namespace delta {

// §11.5.1: the declared bit range that a bit-select or part-select resolves its
// indices against. "The actual bit that is accessed by an address is, in part,
// determined by the declaration": `logic [15:0] acc` and `logic [2:17] acc` are
// both sixteen bits wide, and the same value of an index addresses a different
// bit of each. The bounds are kept as written rather than sorted, because which
// one is the least significant end follows from the order.
//
// This lives in src/common/ so that the elaborator, the simulator and the
// synthesizer answer which bit a select names from one definition. Two of them
// held a copy each, and a correction to either left the other answering the
// declaration differently, which is a netlist disagreeing with the simulation
// of the same source.
struct PackedRange {
  int64_t left = 0;
  int64_t right = 0;

  // The range of a value with no declaration of its own -- a concatenation, a
  // literal, a function result, an `int`, a scalar -- which is addressed as
  // [width-1:0], so an index and an offset are the same number. A width of
  // zero, which a name that resolves to no signal at all reports, yields [0:0]
  // rather than [-1:0]: the value has no bits to address either way, and a left
  // bound below the right one would read as an ascending range and invert the
  // mapping.
  static PackedRange Implicit(uint32_t width) {
    return {width == 0 ? 0 : static_cast<int64_t>(width) - 1, 0};
  }

  int64_t LowIndex() const { return std::min(left, right); }
  int64_t HighIndex() const { return std::max(left, right); }

  // Whether `idx` addresses a bit of the range. §11.5.1 gives an out-of-bounds
  // bit-select the value x for a four-state vector and 0 for a two-state one,
  // and leaves an out-of-bounds write with no effect.
  bool Contains(int64_t idx) const {
    return idx >= LowIndex() && idx <= HighIndex();
  }

  // `idx` brought inside the range, so that a part-select running off one end
  // covers only the bits that are in range (§11.5.1).
  int64_t Clamp(int64_t idx) const {
    return std::clamp(idx, LowIndex(), HighIndex());
  }

  // How far above the least significant end of the range `idx` sits. The
  // right-hand bound is that end whichever way the range runs: §11.5.1 reads
  // `logic [0:31] b_vect; b_vect[0 +: 8]` as `b_vect[0:7]`, ascending the range
  // from a base that "shall address a more significant bit than the second"
  // expression, so index 31 of that declaration is its least significant bit.
  //
  // The mapping is linear rather than clamped, so an `idx` outside the range
  // comes back negative or at least its span, and a select running off either
  // end can be told which of its bits are out of range.
  int64_t OffsetOf(int64_t idx) const {
    return (left >= right) ? idx - right : right - idx;
  }

  // The index naming the bit that sits `offset` places above the least
  // significant end of the range, which is the inverse of OffsetOf.
  int64_t IndexAtOffset(int64_t offset) const {
    return (left >= right) ? right + offset : right - offset;
  }

  // The base index an ascending indexed part-select `[base +: width]` is
  // written with to cover the `width` bits starting `offset` above the least
  // significant end. §11.5.1 gives that form the indices `base` through
  // `base + width - 1`, so the base is the numerically lower of the two ends
  // whichever way the declaration runs.
  int64_t PlusSelectBase(int64_t offset, int64_t width) const {
    return (left >= right) ? right + offset : right - offset - width + 1;
  }
};

// The two declared indices a part-select addresses, together with the width its
// syntax states. An indexed part-select spells the width out and it "shall be a
// positive constant"; a non-indexed part-select carries no separate width and
// reports 1, which is never the zero that is rejected.
struct PartSelectIndices {
  int64_t first = 0;
  int64_t second = 0;
  int64_t declared_width = 1;
};

// The storage bits a part-select covers: an offset above the least significant
// end of the vector, and a bit count. A width of zero means the select lies
// wholly outside the vector, which §11.5.1 makes read as x and write nothing.
struct PartSelectBits {
  uint32_t lo = 0;
  uint32_t width = 0;
};

// The pair of declared indices a part-select expression addresses. `idx` is its
// first index expression and `end_val` the second, which is a width for an
// indexed part-select and an index for a non-indexed one. `is_plus` and
// `is_minus` are the two indexed forms §11.5.1 defines, and both false is the
// non-indexed form; they are passed rather than the expression itself so that
// this header depends on nothing above src/common/.
//
// An indexed part-select counts its width along the declared range in whichever
// direction that runs: §11.5.1 reads `a_vect[0 +: 8]` as `a_vect[7:0]` for
// `logic [31:0] a_vect` and `b_vect[0 +: 8]` as `b_vect[0:7]` for
// `logic [0:31] b_vect`, both of them the eight indices 0 through 7.
inline PartSelectIndices PartSelectTargetIndices(int64_t idx, int64_t end_val,
                                                 bool is_plus, bool is_minus) {
  if (is_plus) return {idx, idx + end_val - 1, end_val};
  if (is_minus) return {idx - end_val + 1, idx, end_val};
  return {idx, end_val, 1};
}

// Where the declared indices `first` and `second` land in storage, resolved
// against `range`. Both are brought inside the range first, so a part-select
// that runs off one end covers "only the bits that are in range"; one that
// misses the range entirely covers none.
inline PartSelectBits PartSelectStorageBits(const PackedRange& range,
                                            int64_t first, int64_t second) {
  int64_t lo_idx = std::min(first, second);
  int64_t hi_idx = std::max(first, second);
  if (hi_idx < range.LowIndex() || lo_idx > range.HighIndex()) return {0, 0};
  auto a = static_cast<uint32_t>(range.OffsetOf(range.Clamp(lo_idx)));
  auto b = static_cast<uint32_t>(range.OffsetOf(range.Clamp(hi_idx)));
  uint32_t lo = std::min(a, b);
  return {lo, std::max(a, b) - lo + 1};
}

}  // namespace delta
