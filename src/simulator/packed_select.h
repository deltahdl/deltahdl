#pragma once

#include <algorithm>
#include <cstdint>

#include "parser/ast.h"
#include "simulator/variable.h"

namespace delta {

// §11.5.1 vector bit-select and part-select addressing: turning the indices a
// select is written with into the storage bits it covers. Shared by the read
// path (eval_select.cpp) and the write path (statement_assign.cpp) so that the
// two cannot disagree about which bits an address names.

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
// indexed part-select and an index for a non-indexed one. An indexed
// part-select counts its width along the declared range in whichever direction
// that runs: §11.5.1 reads `a_vect[0 +: 8]` as `a_vect[7:0]` for
// `logic [31:0] a_vect` and `b_vect[0 +: 8]` as `b_vect[0:7]` for
// `logic [0:31] b_vect`, both of them the eight indices 0 through 7.
inline PartSelectIndices PartSelectTargetIndices(const Expr* sel, int64_t idx,
                                                 int64_t end_val) {
  if (sel->is_part_select_plus) return {idx, idx + end_val - 1, end_val};
  if (sel->is_part_select_minus) return {idx - end_val + 1, idx, end_val};
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
