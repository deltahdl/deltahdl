#include <gtest/gtest.h>

#include "simulator/svdpi.h"

// Annex H.12.2 - Array querying functions.
//
// H.12.2 defines the DPI C-layer functions used to inquire about the
// dimensions of an open array: svLeft, svRight, svLow, svHigh, svIncrement,
// svSize (each taking a handle and a dimension index) and svDimensions (taking
// only a handle). Two normative statements govern them:
//
//   Q1 - they are modeled on the SystemVerilog array querying functions and use
//        the same semantics (see 20.7);
//   Q2 - a dimension argument of 0 refers to the packed part of the array
//        (which is one-dimensional) and dimensions greater than 0 refer to the
//        unpacked part.
//
// These tests build an svOpenArrayHandle backed by an svOpenArrayDesc carrying
// distinct packed and unpacked ranges and observe the svdpi.cpp query functions
// applying those two rules.

namespace {

svOpenArrayHandle MakeHandle(const svOpenArrayDimRange* ranges, int n_dims,
                             svOpenArrayDesc* desc) {
  desc->data = nullptr;
  desc->n_dims = n_dims;
  desc->ranges = ranges;
  return desc;
}

// Q2: the dimension index selects which part of the array is queried -
// dimension 0 returns the packed range while dimensions greater than 0 return
// successive unpacked ranges, never confusing one for another. The handle
// models: logic [15:0] arr [0:7] [-1:-8].
TEST(ArrayQueryingFunctions, DimensionZeroIsPackedPart) {
  const svOpenArrayDimRange ranges[] = {{15, 0}, {0, 7}, {-1, -8}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(ranges, 3, &desc);

  // Dimension 0 is the packed part [15:0].
  EXPECT_EQ(svLeft(h, 0), 15);
  EXPECT_EQ(svRight(h, 0), 0);

  // Dimensions > 0 are the unpacked parts, in declaration order.
  EXPECT_EQ(svLeft(h, 1), 0);
  EXPECT_EQ(svRight(h, 1), 7);
  EXPECT_EQ(svLeft(h, 2), -1);
  EXPECT_EQ(svRight(h, 2), -8);
}

// Q1: low/high/size derive from the bounds exactly as 20.7 prescribes - low is
// the smaller bound, high the larger, size the element count - for an ascending
// unpacked range.
TEST(ArrayQueryingFunctions, LowHighSizeMatchTwentySevenSemanticsAscending) {
  const svOpenArrayDimRange ranges[] = {{15, 0}, {0, 7}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(ranges, 2, &desc);

  // Unpacked [0:7]: low=0, high=7, size=8.
  EXPECT_EQ(svLow(h, 1), 0);
  EXPECT_EQ(svHigh(h, 1), 7);
  EXPECT_EQ(svSize(h, 1), 8);
}

// Q1: the same derivations hold for the descending packed range, and for a
// range whose bounds are negative - low/high are orientation-independent.
TEST(ArrayQueryingFunctions, LowHighSizeMatchTwentySevenSemanticsDescending) {
  const svOpenArrayDimRange ranges[] = {{15, 0}, {-1, -8}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(ranges, 2, &desc);

  // Packed [15:0]: low=0, high=15, size=16.
  EXPECT_EQ(svLow(h, 0), 0);
  EXPECT_EQ(svHigh(h, 0), 15);
  EXPECT_EQ(svSize(h, 0), 16);

  // Unpacked [-1:-8]: low=-8, high=-1, size=8.
  EXPECT_EQ(svLow(h, 1), -8);
  EXPECT_EQ(svHigh(h, 1), -1);
  EXPECT_EQ(svSize(h, 1), 8);
}

// Q1: svIncrement follows 20.7's $increment - it is 1 when the left bound is
// greater than or equal to the right bound (a descending range) and -1
// otherwise (an ascending range).
TEST(ArrayQueryingFunctions, IncrementMatchesTwentySevenSemantics) {
  const svOpenArrayDimRange ranges[] = {{15, 0}, {0, 7}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(ranges, 2, &desc);

  EXPECT_EQ(svIncrement(h, 0), 1);   // [15:0] descending -> +1
  EXPECT_EQ(svIncrement(h, 1), -1);  // [0:7] ascending  -> -1
}

// Q1/Q2: svDimensions reports the total number of queryable dimensions - the
// single packed dimension plus every unpacked dimension - so that valid
// dimension arguments span 0 .. svDimensions-1.
TEST(ArrayQueryingFunctions, DimensionsCountsPackedPlusUnpacked) {
  const svOpenArrayDimRange ranges[] = {{15, 0}, {0, 7}, {-1, -8}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(ranges, 3, &desc);

  // One packed part + two unpacked parts.
  EXPECT_EQ(svDimensions(h), 3);
}

// Q1 edge case: a single-element range [0:0] degenerates correctly - left and
// right coincide, so low == high, size is 1, and the bound-equal case of
// $increment yields +1.
TEST(ArrayQueryingFunctions, DegenerateSingleElementRange) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 0}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(ranges, 2, &desc);

  EXPECT_EQ(svLow(h, 0), 0);
  EXPECT_EQ(svHigh(h, 0), 0);
  EXPECT_EQ(svSize(h, 0), 1);
  EXPECT_EQ(svIncrement(h, 0), 1);  // left >= right -> +1
}

// Q2/Q3 error path: only the dimension indices in the valid span are
// addressable (0 for the packed part, 1 .. svDimensions-1 for the unpacked
// parts). A query against an index outside that span - or against a null handle
// - resolves no range, so the functions fall back to safe defaults rather than
// reading past the descriptor. This exercises the handle/dimension guard in
// production.
TEST(ArrayQueryingFunctions, OutOfRangeDimensionAndNullHandle) {
  const svOpenArrayDimRange ranges[] = {{15, 0}, {0, 7}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(ranges, 2, &desc);

  // Index at and beyond the dimension count, and a negative index, are invalid.
  EXPECT_EQ(svLeft(h, 2), 0);
  EXPECT_EQ(svRight(h, 5), 0);
  EXPECT_EQ(svLow(h, -1), 0);
  EXPECT_EQ(svHigh(h, 2), 0);
  EXPECT_EQ(svSize(h, 2), 0);
  EXPECT_EQ(svIncrement(h, 2), 0);  // no range -> neither +1 nor -1

  // A null handle has no dimensions and answers every query with the default.
  EXPECT_EQ(svDimensions(nullptr), 0);
  EXPECT_EQ(svLeft(nullptr, 0), 0);
  EXPECT_EQ(svSize(nullptr, 0), 0);
  EXPECT_EQ(svIncrement(nullptr, 0), 0);
}

}  // namespace
