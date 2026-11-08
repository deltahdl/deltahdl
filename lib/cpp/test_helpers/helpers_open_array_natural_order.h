#pragma once

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdlib>

#include "simulator/svdpi.h"

inline void ExpectUnpackedNaturalOrderMinToZeroMaxToAbs(svOpenArrayHandle h,
                                                        int dim, int l, int r) {
  const int kLo = svLow(h, dim);
  const int kHi = svHigh(h, dim);
  const int kAbsSpan = std::abs(l - r);

  EXPECT_EQ(kLo, std::min(l, r));
  EXPECT_EQ(kHi, std::max(l, r));
  EXPECT_EQ(svSize(h, dim), kAbsSpan + 1);

  EXPECT_EQ(std::min(l, r) - kLo, 0);
  EXPECT_EQ(kHi - kLo, kAbsSpan);
}
