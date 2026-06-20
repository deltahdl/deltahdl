#include <gtest/gtest.h>

#include "simulator/svdpi.h"

// Annex H.7.5 - Normalized and linearized ranges.
//
// H.7.5 defines two C-layer access conventions for array arguments. A packed
// array is treated as one-dimensional and is indexed with a normalized range
// [n-1:0]: the normalized index 0 names the least-significant bit and n-1 names
// the most-significant bit, independent of the original SystemVerilog range.
// Normalized ranges are used for accessing all array arguments (the lone
// exception, the unpacked dimensions of open arrays, is covered by the open
// array utilities of H.12.2 and is not exercised here).
//
// Linearizing a packed array of dimension sizes (i, j, k) treats it as a single
// dimension of size i*j*k laid out exactly as the multidimensional array stored
// in row-major order. A reference myArray[l][m][n] over normalized ranges maps
// to the linearized index (n + m*k + l*j*k); user C code computes that index
// and reaches the element through the flat normalized accessors. These tests
// play the role of that user C code and observe the layout realized by the
// canonical svdpi.cpp accessors (word = i/32, bit = i%32, least-significant
// group first).

namespace {

// N1/N3: the packed part is accessed as one flat dimension with a normalized
// [n-1:0] range. Normalized index 0 is the least-significant bit and lands in
// the first canonical word, while the top normalized index n-1 lands in the
// most-significant occupied word, matching word = index/32, bit = index%32.
TEST(NormalizedLinearizedRanges, PackedPartIndexedFromLeastSignificantBit) {
  // A 40-bit packed array spans two canonical 32-bit elements (n = 40).
  const int kN = 40;
  svBitVecVal vec[2] = {0u, 0u};

  // Normalized index 0 - the LSB end of the [n-1:0] range.
  svPutBitselBit(vec, 0, 1);
  // Normalized index n-1 - the MSB end of the [n-1:0] range.
  svPutBitselBit(vec, kN - 1, 1);

  EXPECT_EQ(svGetBitselBit(vec, 0), 1u);
  EXPECT_EQ(svGetBitselBit(vec, kN - 1), 1u);

  // Index 0 sits in word 0 bit 0; index 39 sits in word 1 bit 7.
  EXPECT_EQ(vec[0], 1u);
  EXPECT_EQ(vec[1], 1u << 7);
}

// N6/N7: the worked linearization example. For normalized packed dimension
// sizes (i, j, k), the reference myArray[l][m][n] maps to the flat index (n +
// m*k + l*j*k). Advancing the last index by one moves a single bit, advancing
// the middle index moves by k, and advancing the first index moves by j*k - the
// signature of a row-major layout where the last subscript varies fastest.
TEST(NormalizedLinearizedRanges, LinearizedReferenceFollowsRowMajorFormula) {
  const int kI = 2, kJ = 3, kK = 4;  // 24-bit packed array, one canonical word.
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  EXPECT_EQ(linear(1, 2, 3), 23);  // last element of the linearized array.
  EXPECT_EQ(linear(1, 2, 3) - linear(1, 2, 2), 1);   // step in n is 1 bit.
  EXPECT_EQ(linear(1, 2, 3) - linear(1, 1, 3), kK);  // step in m is k bits.
  EXPECT_EQ(linear(1, 2, 3) - linear(0, 2, 3), kJ * kK);  // step in l is j*k.

  // Writing through the computed flat index and reading it back proves the
  // formula addresses exactly one canonical bit and nothing else.
  svBitVecVal vec = 0u;
  svPutBitselBit(&vec, linear(1, 1, 2), 1);  // 2 + 4 + 12 = 18
  for (int b = 0; b < kI * kJ * kK; ++b) {
    EXPECT_EQ(svGetBitselBit(&vec, b), b == 18 ? 1u : 0u);
  }
}

// N1/N6: "the one-dimensional array has the same layout as the corresponding
// multidimensional array stored in row-major order." Iterating the dimensions
// in nested row-major order yields linearized indices 0,1,2,... contiguously,
// i.e., the linearized view and a plain one-dimensional array coincide bit for
// bit.
TEST(NormalizedLinearizedRanges, RowMajorIterationIsContiguousOneDimensional) {
  const int kI = 2, kJ = 3, kK = 4;
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  svBitVecVal vec = 0u;
  int counter = 0;
  // Row-major nesting: the last subscript (n) is the innermost loop.
  for (int l = 0; l < kI; ++l) {
    for (int m = 0; m < kJ; ++m) {
      for (int n = 0; n < kK; ++n) {
        EXPECT_EQ(linear(l, m, n), counter);  // contiguous, no gaps/overlaps.
        svPutBitselBit(&vec, linear(l, m, n), counter & 1);
        ++counter;
      }
    }
  }
  EXPECT_EQ(counter, kI * kJ * kK);

  // Read straight down the flat one-dimensional index: each bit equals the
  // alternating pattern written in row-major order.
  for (int b = 0; b < kI * kJ * kK; ++b) {
    EXPECT_EQ(svGetBitselBit(&vec, b), static_cast<svBit>(b & 1));
  }
}

// N1/N6 edge: a linearized index past 31 falls into the next canonical 32-bit
// element, confirming the flat one-dimensional array spans multiple canonical
// words exactly as the packed-array canonical representation of H.7.7
// prescribes.
TEST(NormalizedLinearizedRanges, LinearizedIndexCrossesCanonicalWordBoundary) {
  const int kI = 2, kJ = 2,
            kK = 20;  // 80-bit packed array, three canonical words.
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  svBitVecVal vec[3] = {0u, 0u, 0u};

  // (0,1,12) -> 12 + 20 = 32: the first bit of the second canonical word.
  const int kIdxLo = linear(0, 1, 12);
  EXPECT_EQ(kIdxLo, 32);
  svPutBitselBit(vec, kIdxLo, 1);
  EXPECT_EQ(vec[0], 0u);
  EXPECT_EQ(vec[1], 1u);

  // (1,1,19) -> 19 + 20 + 40 = 79: the final bit, in the third canonical word.
  const int kIdxHi = linear(1, 1, 19);
  EXPECT_EQ(kIdxHi, 79);
  svPutBitselBit(vec, kIdxHi, 1);
  EXPECT_EQ(vec[2], 1u << 15);  // 79 % 32 = 15

  EXPECT_EQ(svGetBitselBit(vec, kIdxLo), 1u);
  EXPECT_EQ(svGetBitselBit(vec, kIdxHi), 1u);
}

// N6/N1 (element granularity): linearization is not limited to single bits - a
// whole k-bit row of a row-major packed array of dimension sizes (i, j, k)
// lives at the flat offset (m*k + l*j*k). The part-select accessors read and
// write that row directly at its computed normalized offset, treating the
// multidimensional packed array as one flat dimension.
TEST(NormalizedLinearizedRanges, LinearizedElementFieldAccessedByPartSelect) {
  const int kI = 2, kJ = 3, kK = 4;  // 24-bit packed array, one canonical word.
  auto row_offset = [&](int l, int m) { return m * kK + l * kJ * kK; };

  svBitVecVal vec = 0u;
  // Write a distinct k-bit value into each row, visiting rows in row-major
  // order.
  svBitVecVal value = 1u;
  for (int l = 0; l < kI; ++l) {
    for (int m = 0; m < kJ; ++m) {
      svPutPartselBit(&vec, value, row_offset(l, m), kK);
      ++value;
    }
  }

  // Read every row back through the part-select path at its linearized offset;
  // each k-bit field returns exactly the value written to that row.
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

// N3/N4/N7 (4-state breadth): normalized ranges and the row-major linearization
// formula apply to all array arguments, not only the 2-state array used in the
// worked example. Logic values placed at the flat indices (n + m*k + l*j*k) are
// recovered through the logic bit-select accessors with full 0/1/x/z fidelity,
// and no other position is disturbed.
TEST(NormalizedLinearizedRanges,
     FourStateLinearizedAccessPreservesLogicValues) {
  const int kI = 2, kJ = 2,
            kK = 3;  // 12-bit 4-state packed array, one element.
  auto linear = [&](int l, int m, int n) { return n + m * kK + l * kJ * kK; };

  svLogicVecVal vec = {0u, 0u};
  svPutBitselLogic(&vec, linear(0, 0, 0), sv_1);  // index 0
  svPutBitselLogic(&vec, linear(0, 1, 2), sv_z);  // index 5
  svPutBitselLogic(&vec, linear(1, 0, 1), sv_x);  // index 7
  svPutBitselLogic(&vec, linear(1, 1, 2), sv_0);  // index 11

  EXPECT_EQ(svGetBitselLogic(&vec, linear(0, 0, 0)), sv_1);
  EXPECT_EQ(svGetBitselLogic(&vec, linear(0, 1, 2)), sv_z);
  EXPECT_EQ(svGetBitselLogic(&vec, linear(1, 0, 1)), sv_x);
  EXPECT_EQ(svGetBitselLogic(&vec, linear(1, 1, 2)), sv_0);

  // Every unwritten position stays at logic 0, confirming each reference
  // addressed exactly its own linearized bit and nothing adjacent.
  for (int b = 0; b < kI * kJ * kK; ++b) {
    const bool kWritten = b == linear(0, 0, 0) || b == linear(0, 1, 2) ||
                          b == linear(1, 0, 1) || b == linear(1, 1, 2);
    if (!kWritten) EXPECT_EQ(svGetBitselLogic(&vec, b), sv_0);
  }
}

}  // namespace
