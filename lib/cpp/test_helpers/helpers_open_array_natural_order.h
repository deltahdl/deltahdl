#pragma once

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdlib>

#include "simulator/svdpi.h"

// Shared verification for the Annex H.7.3 / H.7.6 "natural element order" rule:
// for an unpacked dimension declared [L:R], svLow / svHigh / svSize report
// min(L,R) / max(L,R) / abs(L-R)+1, and an element's C index is its
// SystemVerilog index minus svLow, so min(L,R) -> C index 0 and max(L,R) ->
// C index abs(L-R). Used by the H.7.3 and H.7.6 unit tests, which build the
// open-array handle slightly differently but observe the identical mapping.
inline void ExpectUnpackedNaturalOrderMinToZeroMaxToAbs(svOpenArrayHandle h,
                                                        int dim, int l, int r) {
  const int kLo = svLow(h, dim);   // min(L,R)
  const int kHi = svHigh(h, dim);  // max(L,R)
  const int kAbsSpan = std::abs(l - r);

  EXPECT_EQ(kLo, std::min(l, r));           // svLow == min(L,R).
  EXPECT_EQ(kHi, std::max(l, r));           // svHigh == max(L,R).
  EXPECT_EQ(svSize(h, dim), kAbsSpan + 1);  // count == abs(L-R)+1.

  EXPECT_EQ(std::min(l, r) - kLo, 0);  // element at min(L,R) -> C index 0.
  EXPECT_EQ(kHi - kLo, kAbsSpan);  // element at max(L,R) -> C index abs(L-R).
}
