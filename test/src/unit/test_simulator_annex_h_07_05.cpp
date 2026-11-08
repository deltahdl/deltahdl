#include <gtest/gtest.h>

#include "simulator/svdpi.h"

namespace {

TEST(NormalizedLinearizedRanges, PackedPartIndexedFromLeastSignificantBit) {
  const int kN = 40;
  svBitVecVal vec[2] = {0u, 0u};

  svPutBitselBit(vec, 0, 1);
  svPutBitselBit(vec, kN - 1, 1);

  EXPECT_EQ(svGetBitselBit(vec, 0), 1u);
  EXPECT_EQ(svGetBitselBit(vec, kN - 1), 1u);

  EXPECT_EQ(vec[0], 1u);
  EXPECT_EQ(vec[1], 1u << 7);
}

TEST(NormalizedLinearizedRanges, LinearizedReferenceFollowsRowMajorFormula) {
  const int kI = 2, kJ = 3, kK = 4;
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  EXPECT_EQ(linear(1, 2, 3), 23);
  EXPECT_EQ(linear(1, 2, 3) - linear(1, 2, 2), 1);
  EXPECT_EQ(linear(1, 2, 3) - linear(1, 1, 3), kK);
  EXPECT_EQ(linear(1, 2, 3) - linear(0, 2, 3), kJ * kK);

  svBitVecVal vec = 0u;
  svPutBitselBit(&vec, linear(1, 1, 2), 1);
  for (int b = 0; b < kI * kJ * kK; ++b) {
    EXPECT_EQ(svGetBitselBit(&vec, b), b == 18 ? 1u : 0u);
  }
}

TEST(NormalizedLinearizedRanges, RowMajorIterationIsContiguousOneDimensional) {
  const int kI = 2, kJ = 3, kK = 4;
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  svBitVecVal vec = 0u;
  int counter = 0;
  for (int l = 0; l < kI; ++l) {
    for (int m = 0; m < kJ; ++m) {
      for (int n = 0; n < kK; ++n) {
        EXPECT_EQ(linear(l, m, n), counter);
        svPutBitselBit(&vec, linear(l, m, n), counter & 1);
        ++counter;
      }
    }
  }
  EXPECT_EQ(counter, kI * kJ * kK);

  for (int b = 0; b < kI * kJ * kK; ++b) {
    EXPECT_EQ(svGetBitselBit(&vec, b), static_cast<svBit>(b & 1));
  }
}

TEST(NormalizedLinearizedRanges, LinearizedIndexCrossesCanonicalWordBoundary) {
  const int kJ = 2, kK = 20;
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  svBitVecVal vec[3] = {0u, 0u, 0u};

  const int kIdxLo = linear(0, 1, 12);
  EXPECT_EQ(kIdxLo, 32);
  svPutBitselBit(vec, kIdxLo, 1);
  EXPECT_EQ(vec[0], 0u);
  EXPECT_EQ(vec[1], 1u);

  const int kIdxHi = linear(1, 1, 19);
  EXPECT_EQ(kIdxHi, 79);
  svPutBitselBit(vec, kIdxHi, 1);
  EXPECT_EQ(vec[2], 1u << 15);

  EXPECT_EQ(svGetBitselBit(vec, kIdxLo), 1u);
  EXPECT_EQ(svGetBitselBit(vec, kIdxHi), 1u);
}

TEST(NormalizedLinearizedRanges, LinearizedElementFieldAccessedByPartSelect) {
  const int kI = 2, kJ = 3, kK = 4;
  auto row_offset = [&](int l, int m) { return m * kK + l * kJ * kK; };

  svBitVecVal vec = 0u;
  svBitVecVal value = 1u;
  for (int l = 0; l < kI; ++l) {
    for (int m = 0; m < kJ; ++m) {
      svPutPartselBit(&vec, value, row_offset(l, m), kK);
      ++value;
    }
  }

  value = 1u;
  for (int l = 0; l < kI; ++l) {
    for (int m = 0; m < kJ; ++m) {
      svBitVecVal out = 0u;
      svGetPartselBit(&out, &vec, row_offset(l, m), kK);
      EXPECT_EQ(out, value & SV_MASK(kK));
      ++value;
    }
  }
}

TEST(NormalizedLinearizedRanges,
     FourStateLinearizedAccessPreservesLogicValues) {
  const int kI = 2, kJ = 2, kK = 3;
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  svLogicVecVal vec = {0u, 0u};
  svPutBitselLogic(&vec, linear(0, 0, 0), sv_1);
  svPutBitselLogic(&vec, linear(0, 1, 2), sv_z);
  svPutBitselLogic(&vec, linear(1, 0, 1), sv_x);
  svPutBitselLogic(&vec, linear(1, 1, 2), sv_0);

  EXPECT_EQ(svGetBitselLogic(&vec, linear(0, 0, 0)), sv_1);
  EXPECT_EQ(svGetBitselLogic(&vec, linear(0, 1, 2)), sv_z);
  EXPECT_EQ(svGetBitselLogic(&vec, linear(1, 0, 1)), sv_x);
  EXPECT_EQ(svGetBitselLogic(&vec, linear(1, 1, 2)), sv_0);

  for (int b = 0; b < kI * kJ * kK; ++b) {
    const bool kWritten = b == linear(0, 0, 0) || b == linear(0, 1, 2) ||
                          b == linear(1, 0, 1) || b == linear(1, 1, 2);
    if (!kWritten) {
      EXPECT_EQ(svGetBitselLogic(&vec, b), sv_0);
    }
  }
}

}  // namespace
