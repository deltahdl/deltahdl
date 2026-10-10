#pragma once

#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;

// §7.8.1, §7.8.4 and §7.8.5: an integral index of an associative array, kept
// whole however wide its type is. Two indices that differ in any bit are two
// entries, and the entries are ordered by numerical value: the index is held
// as a signed integer of unbounded width, the value an index of an unsigned
// type or a wildcard index has being never negative, so one ordering serves
// both. An int64_t key kept only the low 64 bits, so indices differing above
// bit 63 were one entry, and ordered a 64-bit unsigned index with bit 63 set
// before every small one.
class AssocIndex {
 public:
  AssocIndex() = default;
  // The index whose value is `value`, the number an index of a 64-bit signed
  // type holds.
  AssocIndex(int64_t value);

  // §7.8.4: the index `val` gives an array whose index type is `index_width`
  // bits wide, signed when `is_signed`: `val` cut to that width and then sign-
  // or zero-extended by the type. §7.8.1: a wildcard index keeps the
  // self-determined value of `val`, unsigned, so equal values of differing
  // widths are one index. An x or z bit reads as 0.
  static AssocIndex Of(const Logic4Vec& val, bool is_wildcard,
                       uint32_t index_width, bool is_signed);

  // The index as a value `width` bits wide and signed when `is_signed`, as an
  // index variable of the array's index type holds it.
  Logic4Vec ToVec(Arena& arena, uint32_t width, bool is_signed) const;

  // The low 64 bits of the index, two's complement: the whole index where it
  // lies between INT64_MIN and INT64_MAX.
  int64_t Low() const { return low_; }

  // The index as a signed value of as many whole words as it holds, which
  // reads as its own number whatever the array's index type is: what %p prints
  // for the key (§21.2.1.6).
  Logic4Vec ToSignedVec(Arena& arena) const;

  friend bool operator<(const AssocIndex& a, const AssocIndex& b);
  friend bool operator==(const AssocIndex& a, const AssocIndex& b) {
    return a.low_ == b.low_ && a.high_ == b.high_;
  }

 private:
  // Bits 0 to 63 of the value, and the 64-bit words above them least
  // significant first, two's complement, with every word at the top that
  // only repeats the sign of the word below it dropped, so that one value has
  // one representation and a value that fits int64_t has no high words.
  int64_t low_ = 0;
  std::vector<uint64_t> high_;

  void Trim();
  bool IsNegative() const;
  uint64_t Word(size_t i) const;
  size_t WordCount() const { return high_.size() + 1; }
};

}  // namespace delta
