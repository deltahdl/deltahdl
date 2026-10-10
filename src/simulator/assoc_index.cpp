#include "simulator/assoc_index.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"

namespace delta {

namespace {

constexpr uint64_t kAllOnes = ~uint64_t{0};

// Word `i` of `val`, extended past its width by its own signedness, x and z
// bits read as 0: what a cast of `val` to a wider type reads there (§6.24.1).
uint64_t ExtendedWord(const Logic4Vec& val, size_t i) {
  size_t count = (val.width + 63) / 64;
  uint32_t top_bits = val.width % 64;
  auto known = [&](size_t w) { return val.words[w].aval & ~val.words[w].bval; };
  bool negative =
      val.is_signed && ((known(count - 1) >> ((val.width - 1) % 64)) & 1) != 0;
  if (i >= count) return negative ? kAllOnes : 0;
  uint64_t word = known(i);
  if (i + 1 == count && top_bits != 0) {
    uint64_t mask = (uint64_t{1} << top_bits) - 1;
    word = negative ? (word | ~mask) : (word & mask);
  }
  return word;
}

}  // namespace

AssocIndex::AssocIndex(int64_t value) : low_(value) {}

AssocIndex AssocIndex::Of(const Logic4Vec& val, bool is_wildcard,
                          uint32_t index_width, bool is_signed) {
  uint32_t width = is_wildcard ? val.width : index_width;
  bool type_is_signed = !is_wildcard && is_signed;
  size_t count = std::max<size_t>((width + 63) / 64, 1);
  std::vector<uint64_t> words(count + 1, 0);
  for (size_t i = 0; i < count; ++i) words[i] = ExtendedWord(val, i);
  // The cast to the index type: cut to its width, then extended by its
  // signedness. An unsigned value keeps the zero word above it, so its top bit
  // is never read as a sign.
  uint32_t top_bits = width % 64;
  uint64_t& top = words[count - 1];
  uint32_t sign_bit = top_bits == 0 ? 63 : top_bits - 1;
  bool negative = type_is_signed && ((top >> sign_bit) & 1) != 0;
  if (top_bits != 0) {
    uint64_t mask = (uint64_t{1} << top_bits) - 1;
    top = negative ? (top | ~mask) : (top & mask);
  }
  words[count] = negative ? kAllOnes : 0;
  AssocIndex index;
  index.low_ = static_cast<int64_t>(words[0]);
  index.high_.assign(words.begin() + 1, words.end());
  index.Trim();
  return index;
}

void AssocIndex::Trim() {
  while (!high_.empty()) {
    uint64_t below = Word(high_.size() - 1);
    uint64_t sign = (below >> 63) != 0 ? kAllOnes : 0;
    if (high_.back() != sign) break;
    high_.pop_back();
  }
}

bool AssocIndex::IsNegative() const {
  return (Word(WordCount() - 1) >> 63) != 0;
}

uint64_t AssocIndex::Word(size_t i) const {
  return i == 0 ? static_cast<uint64_t>(low_) : high_[i - 1];
}

Logic4Vec AssocIndex::ToVec(Arena& arena, uint32_t width,
                            bool is_signed) const {
  Logic4Vec vec = MakeLogic4Vec(arena, width);
  uint64_t fill = IsNegative() ? kAllOnes : 0;
  for (size_t i = 0; i < vec.nwords; ++i) {
    vec.words[i].aval = i < WordCount() ? Word(i) : fill;
    vec.words[i].bval = 0;
  }
  if (width % 64 != 0)
    vec.words[vec.nwords - 1].aval &= (uint64_t{1} << (width % 64)) - 1;
  vec.is_signed = is_signed;
  return vec;
}

Logic4Vec AssocIndex::ToSignedVec(Arena& arena) const {
  return ToVec(arena, static_cast<uint32_t>(64 * WordCount()), true);
}

bool operator<(const AssocIndex& a, const AssocIndex& b) {
  bool a_negative = a.IsNegative();
  if (a_negative != b.IsNegative()) return a_negative;
  // Of two values of one sign, the one of more words lies farther from zero.
  if (a.WordCount() != b.WordCount())
    return (a.WordCount() < b.WordCount()) != a_negative;
  for (size_t i = a.WordCount(); i-- > 0;) {
    if (a.Word(i) != b.Word(i)) return a.Word(i) < b.Word(i);
  }
  return false;
}

}  // namespace delta
