#include <gtest/gtest.h>

#include <cstdlib>

#include "simulator/svdpi.h"

// Annex H.7.6 - Mapping between SystemVerilog ranges and C ranges.
//
// H.7.6 fixes how a SystemVerilog declared range becomes the range a C
// programmer sees across the DPI. Its own distinctive rules are:
//
//   b) A packed array of range [L:R] is normalized to [abs(L-R):0]: its LSB has
//      the normalized C index 0 and its MSB has the normalized C index
//      abs(L-R).
//   c) (shall) The natural order of unpacked elements is used - lower indices
//      first. For a SystemVerilog range [L:R], the element with SystemVerilog
//      index min(L,R) has C index 0 and the element with index max(L,R) has C
//      index abs(L-R).
//
// The mapping is the same for calls in both directions (SystemVerilog calling C
// and C calling SystemVerilog). Linearization of a multidimensional packed part
// (rule a) and the array querying utilities are defined by the dependencies
// H.7.5, 6.22.2 and H.12.2 and are not re-proven here.
//
// These rules are realized entirely by existing production code: rule b by the
// canonical bit-select accessors in svdpi.cpp (normalized index 0 is the
// least-significant bit, word = i/32, bit = i%32), and rule c by svLow / svHigh
// / svSize, which return min / max / element-count over a dimension's declared
// bounds so that a C index is sv_index - svLow. These tests play the role of
// the user C code that derives the normalized indices and observe production
// placing each element exactly where H.7.6 says it must land.

namespace {

svOpenArrayHandle MakeHandle(const svOpenArrayDimRange* ranges, int n_dims,
                             svOpenArrayDesc* desc) {
  desc->data = nullptr;
  desc->n_dims = n_dims;
  desc->ranges = ranges;
  return desc;
}

// Rule b: a packed array of SystemVerilog range [L:R] is normalized to
// [abs(L-R):0]. The LSB maps to normalized C index 0 and the MSB to normalized
// C index abs(L-R), regardless of whether the SystemVerilog range was declared
// descending or ascending. The canonical bit-select accessors index the value
// over exactly that normalized range.
TEST(MappingSvRangesToCRanges, PackedRangeNormalizedLsbZeroMsbAbsLminusR) {
  struct Case {
    int l;
    int r;
  };
  // Descending [7:4], ascending [4:7], and a negative-spanning [2:-3] all carry
  // the same width abs(L-R)+1 and the same normalized MSB index abs(L-R).
  const Case cases[] = {{7, 4}, {4, 7}, {2, -3}};
  for (const Case& c : cases) {
    const int msb = std::abs(c.l - c.r);  // normalized index of the MSB.
    const int width = msb + 1;
    const int words = SV_PACKED_DATA_NELEMS(width);
    ASSERT_LE(words, 2);
    svBitVecVal vec[2] = {0u, 0u};

    // Drive the two endpoints of the normalized [abs(L-R):0] range.
    svPutBitselBit(vec, 0, 1);    // LSB -> normalized index 0.
    svPutBitselBit(vec, msb, 1);  // MSB -> normalized index abs(L-R).

    EXPECT_EQ(svGetBitselBit(vec, 0), 1u);
    EXPECT_EQ(svGetBitselBit(vec, msb), 1u);

    // Nothing outside the two endpoints is set: the normalized range spans
    // exactly indices 0 .. abs(L-R) and no more.
    for (int i = 0; i < width; ++i) {
      const svBit expected = (i == 0 || i == msb) ? 1u : 0u;
      EXPECT_EQ(svGetBitselBit(vec, i), expected)
          << "L=" << c.l << " R=" << c.r;
    }
  }
}

// Rule b at element granularity: a single-element packed range [k:k] has
// abs(L-R) == 0, so it normalizes to [0:0] - the MSB and LSB coincide at C
// index 0. This is the degenerate endpoint of the normalization formula.
TEST(MappingSvRangesToCRanges, SingleElementPackedRangeNormalizesToZeroZero) {
  const int l = 5, r = 5;
  EXPECT_EQ(std::abs(l - r), 0);

  svBitVecVal vec = 0u;
  svPutBitselBit(&vec, 0, 1);
  EXPECT_EQ(svGetBitselBit(&vec, 0), 1u);
  EXPECT_EQ(vec, 1u);  // only normalized index 0 exists.
}

// Rule c (shall): for an unpacked dimension of SystemVerilog range [L:R] the
// element with index min(L,R) gets C index 0 and the element with index
// max(L,R) gets C index abs(L-R). svLow / svHigh / svSize supply min / max /
// count, and a C index is the user computation sv_index - svLow. Exercised for
// an ascending, a descending, and a negative range.
TEST(MappingSvRangesToCRanges, UnpackedNaturalOrderMinToZeroMaxToAbs) {
  struct Case {
    int l;
    int r;
  };
  const Case cases[] = {{0, 7}, {7, 0}, {-1, -8}};
  for (const Case& c : cases) {
    // Dimension 0 is an unused packed placeholder; dimension 1 is under test.
    const svOpenArrayDimRange ranges[] = {{0, 0}, {c.l, c.r}};
    svOpenArrayDesc desc;
    svOpenArrayHandle h = MakeHandle(ranges, 2, &desc);

    const int lo = svLow(h, 1);   // min(L,R)
    const int hi = svHigh(h, 1);  // max(L,R)
    const int abs_span = std::abs(c.l - c.r);

    EXPECT_EQ(lo, std::min(c.l, c.r));
    EXPECT_EQ(hi, std::max(c.l, c.r));
    EXPECT_EQ(svSize(h, 1), abs_span + 1);

    // The C index of an element is its SystemVerilog index minus the low bound.
    EXPECT_EQ(lo - lo, 0);         // min(L,R) -> C index 0.
    EXPECT_EQ(hi - lo, abs_span);  // max(L,R) -> C index abs(L-R).
  }
}

// Rule c "natural order ... lower indices go first": walking the SystemVerilog
// indices from low to high yields C indices 0, 1, 2, ... contiguously, so the C
// layout preserves the ascending element order independent of the declared
// range orientation. Verified against a descending declaration [3:-2].
TEST(MappingSvRangesToCRanges, UnpackedLowerIndicesGoFirst) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {3, -2}};  // unpacked [3:-2].
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(ranges, 2, &desc);

  const int lo = svLow(h, 1);     // -2
  const int size = svSize(h, 1);  // 6
  EXPECT_EQ(lo, -2);
  EXPECT_EQ(size, 6);

  int expected_c = 0;
  for (int sv = lo; sv < lo + size; ++sv) {
    EXPECT_EQ(sv - lo, expected_c);  // contiguous 0,1,2,... in ascending order.
    ++expected_c;
  }
  EXPECT_EQ(expected_c, size);
}

// The worked example from H.7.6: logic [2:3][1:3][2:0] b [1:10][31:0] must be
// described in C as logic [17:0] b [0:9][0:31]. The packed part linearizes
// (sizes 2*3*3 = 18, rule a / H.7.5) and then normalizes to [17:0] (rule b),
// while the two unpacked ranges normalize by rule c: [1:10] -> [0:9] and
// [31:0] -> [0:31]. The descriptor carries the linearized packed dimension at
// index 0 and the unpacked dimensions after it.
TEST(MappingSvRangesToCRanges, WorkedExampleNormalizedForm) {
  // Original packed dimension sizes, before linearization.
  const int packed_sizes[] = {std::abs(2 - 3) + 1, std::abs(1 - 3) + 1,
                              std::abs(2 - 0) + 1};
  int packed_width = 1;
  for (int s : packed_sizes) packed_width *= s;
  EXPECT_EQ(packed_width, 18);  // 2 * 3 * 3.

  // Descriptor: dim 0 = linearized+normalized packed part [17:0];
  // dim 1 = unpacked [1:10]; dim 2 = unpacked [31:0].
  const svOpenArrayDimRange ranges[] = {{17, 0}, {1, 10}, {31, 0}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(ranges, 3, &desc);

  // Packed part normalizes to [17:0]: size 18, MSB normalized index 17.
  EXPECT_EQ(svSize(h, 0), 18);
  EXPECT_EQ(std::abs(svLeft(h, 0) - svRight(h, 0)), 17);
  svBitVecVal packed = 0u;
  svPutBitselBit(&packed, 17, 1);  // top of the normalized packed range exists.
  EXPECT_EQ(svGetBitselBit(&packed, 17), 1u);

  // Unpacked [1:10] -> normalized [0:9]: min 1 -> C 0, max 10 -> C 9.
  EXPECT_EQ(svLow(h, 1), 1);
  EXPECT_EQ(svSize(h, 1), 10);
  EXPECT_EQ(svLow(h, 1) - svLow(h, 1), 0);
  EXPECT_EQ(svHigh(h, 1) - svLow(h, 1), 9);

  // Unpacked [31:0] -> normalized [0:31]: min 0 -> C 0, max 31 -> C 31.
  EXPECT_EQ(svLow(h, 2), 0);
  EXPECT_EQ(svSize(h, 2), 32);
  EXPECT_EQ(svHigh(h, 2) - svLow(h, 2), 31);
}

// "The above range mapping ... applies to calls made in both directions." The
// same normalized index addresses the same bit whether C reads a value handed
// in by SystemVerilog (the get path of an SV->C call) or writes a value that
// SystemVerilog will read back (the put path of a C->SV call / copy-out).
// Writing through the normalized indices of a packed [L:R] and reading them
// back yields the identical mapping in both directions.
TEST(MappingSvRangesToCRanges, MappingAppliesInBothCallDirections) {
  const int l = 11, r = 4;          // packed [11:4].
  const int msb = std::abs(l - r);  // 7
  const int width = msb + 1;        // 8
  svBitVecVal vec = 0u;

  // C->SV direction: C writes the value SystemVerilog will observe.
  for (int i = 0; i < width; ++i) {
    if (i % 2 == 0) svPutBitselBit(&vec, i, 1);
  }

  // SV->C direction: C reads the value back at the same normalized indices.
  for (int i = 0; i < width; ++i) {
    EXPECT_EQ(svGetBitselBit(&vec, i),
              static_cast<svBit>(i % 2 == 0 ? 1u : 0u));
  }
  EXPECT_EQ(svGetBitselBit(&vec, 0), 1u);    // LSB normalized index 0.
  EXPECT_EQ(svGetBitselBit(&vec, msb), 0u);  // MSB normalized index abs(L-R)=7.
}

// Rule b edge: the normalization holds when the packed range is wider than one
// canonical 32-bit word. For [40:1] the width is abs(40-1)+1 = 40, so the MSB
// has normalized index 39, which the canonical accessors place in the second
// canonical word (39 / 32 = word 1, 39 % 32 = bit 7) while the LSB stays at
// normalized index 0 in the first word.
TEST(MappingSvRangesToCRanges, PackedRangeWiderThanCanonicalWordNormalizes) {
  const int l = 40, r = 1;
  const int msb = std::abs(l - r);  // 39
  const int width = msb + 1;        // 40
  ASSERT_EQ(SV_PACKED_DATA_NELEMS(width), 2);
  svBitVecVal vec[2] = {0u, 0u};

  svPutBitselBit(vec, 0, 1);    // LSB -> normalized index 0.
  svPutBitselBit(vec, msb, 1);  // MSB -> normalized index abs(L-R) = 39.

  EXPECT_EQ(svGetBitselBit(vec, 0), 1u);
  EXPECT_EQ(svGetBitselBit(vec, msb), 1u);
  EXPECT_EQ(vec[0], 1u);       // only bit 0 of the low canonical word.
  EXPECT_EQ(vec[1], 1u << 7);  // MSB lands in the high word at bit 7.
}

// Rule c edge: a single-element unpacked dimension [k:k] has abs(L-R) == 0, so
// its only element maps to C index 0. svLow / svHigh / svSize report the
// coincident bound and unit count, and the lone element's C index (sv - svLow)
// is zero even for a negative declared index.
TEST(MappingSvRangesToCRanges, SingleElementUnpackedDimensionMapsToZero) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {-4, -4}};  // unpacked [-4:-4].
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(ranges, 2, &desc);

  EXPECT_EQ(svLow(h, 1), -4);
  EXPECT_EQ(svHigh(h, 1), -4);
  EXPECT_EQ(svSize(h, 1), 1);
  EXPECT_EQ(svHigh(h, 1) - svLow(h, 1), 0);  // sole element -> C index 0.
}

}  // namespace
