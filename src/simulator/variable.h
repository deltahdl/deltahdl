#pragma once

#include <algorithm>
#include <cstdint>
#include <functional>
#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;

// §11.5.1: the declared bit range that a bit-select or part-select resolves its
// indices against. "The actual bit that is accessed by an address is, in part,
// determined by the declaration": `logic [15:0] acc` and `logic [2:17] acc` are
// both sixteen bits wide, and the same value of an index addresses a different
// bit of each. The bounds are kept as written rather than sorted, because which
// one is the least significant end follows from the order.
struct PackedRange {
  int64_t left = 0;
  int64_t right = 0;

  // The range of a value with no declaration of its own -- a concatenation, a
  // function result, an `int`, a scalar -- which is addressed as [width-1:0].
  static PackedRange Implicit(uint32_t width) {
    return {static_cast<int64_t>(width) - 1, 0};
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
};

struct Variable {
  Logic4Vec value{};
  Logic4Vec prev_value{};
  bool is_forced = false;
  Logic4Vec forced_value{};
  Logic4Vec pending_nba{};
  bool has_pending_nba = false;
  bool is_event = false;
  bool is_null_event = false;
  bool is_signed = false;
  bool is_4state = true;
  uint64_t triggered_ticks = UINT64_MAX;

  // §7.4.1: for a packed multidimensional array stored as one flat vector (e.g.
  // `logic [1:0][7:0]`), the bit width of one outermost element. A single-index
  // select `x[i]` then selects that many bits at the element's offset instead
  // of one bit. Zero means an ordinary vector (single-bit selects).
  uint32_t packed_elem_width = 0;

  // §11.5.1: the outermost packed dimension of this variable's declaration,
  // exactly as written, recorded only when the declaration carries one. An
  // `int`, a scalar and a string carry none and are addressed as [width-1:0].
  // For a packed multidimensional array the range indexes elements rather than
  // bits, matching packed_elem_width above.
  bool has_packed_range = false;
  PackedRange packed_range{};

  // The range an index in a select of this variable is resolved against.
  PackedRange DeclaredRange() const {
    return has_packed_range ? packed_range : PackedRange::Implicit(value.width);
  }

  // The range a select addressed by bit resolves against. A packed
  // multidimensional array's declared outer range counts elements rather than
  // bits (§7.4.1), so a select that addresses this variable's bits keeps the
  // flattened [width-1:0] view of it.
  PackedRange BitSelectRange() const {
    if (packed_elem_width > 1) return PackedRange::Implicit(value.width);
    return DeclaredRange();
  }

  const Expr* proc_cont_rhs = nullptr;

  const Expr* assign_cont_rhs = nullptr;

  std::vector<std::function<bool()>> watchers;

  void AddWatcher(std::function<bool()> cb) {
    watchers.push_back(std::move(cb));
  }

  void NotifyWatchers() {
    auto pending = std::move(watchers);
    for (auto& cb : pending) {
      if (!cb()) watchers.push_back(std::move(cb));
    }
  }
};

}  // namespace delta
