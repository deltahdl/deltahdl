#include <gtest/gtest.h>

#include "simulator/svdpi.h"

// Annex H.12.5 - Access to elements via canonical representation.
//
// H.12.5 defines the DPI C-layer functions that copy a whole packed array (a
// single canonical vector) between user space and one element of an open array.
// The svPut*ArrElem*VecVal functions copy from user space into simulator
// storage and the svGet*ArrElem*VecVal functions copy in the other direction,
// for both bit and logic element types and for one, two, or three unpacked
// indices. Its declarative requirements are:
//
//   C1 - the functions copy a whole packed element, in the canonical
//        representation of H.10.1.2, in the direction implied by Put vs Get;
//   C2 - the actual argument's original SystemVerilog ranges index the open
//        array (so a descending or offset unpacked range indexes by its
//        declared coordinates, not by a zero-based position);
//   C3 - the copy spans the element's full width, including multi-word packed
//        elements, and multiple unpacked indices select the element row-major.
//
// These tests build an svOpenArrayHandle backed by a real SvOpenArrayDesc
// buffer and observe the svdpi.cpp copy functions applying those rules.

namespace {

svOpenArrayHandle MakeHandle(void* data, const SvOpenArrayDimRange* ranges,
                             int n_dims, SvOpenArrayDesc* desc) {
  desc->data = data;
  desc->n_dims = n_dims;
  desc->ranges = ranges;
  return desc;
}

bool LogicEq(const svLogicVecVal& a, const svLogicVecVal& b) {
  return a.aval == b.aval && a.bval == b.bval;
}

// C1: a Put then a Get round-trips a single-word bit element through simulator
// storage, and the value lands at the storage slot the index selects. The
// handle models: bit [7:0] arr [0:3].
TEST(ElementCanonicalAccess, BitPutGetRoundTrip) {
  const SvOpenArrayDimRange ranges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  svBitVecVal in = 0xA5u;
  svPutBitArrElem1VecVal(h, &in, 2);

  // The element copied lands at storage position 2 (index 2 of [0:3]).
  EXPECT_EQ(data[2], 0xA5u);
  EXPECT_EQ(data[0], 0u);
  EXPECT_EQ(data[1], 0u);
  EXPECT_EQ(data[3], 0u);

  svBitVecVal out = 0;
  svGetBitArrElem1VecVal(&out, h, 2);
  EXPECT_EQ(out, 0xA5u);
}

// C1, sim->user direction in isolation: seeding the backing store directly
// (without a prior Put) and reading through Get shows that Get genuinely copies
// from simulator storage rather than echoing a just-written value. The handle
// models: logic [7:0] arr [0:3], with distinct values pre-placed per slot.
TEST(ElementCanonicalAccess, GetReadsPreSeededStorage) {
  const SvOpenArrayDimRange ranges[] = {{7, 0}, {0, 3}};
  svLogicVecVal data[4] = {
      {0x10u, 0x01u}, {0x20u, 0x02u}, {0x30u, 0x03u}, {0x40u, 0x04u}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  // Each index reads back exactly the element pre-seeded at its storage slot,
  // both aval and bval lanes.
  for (int i = 0; i < 4; ++i) {
    svLogicVecVal out = {0xFFFFFFFFu, 0xFFFFFFFFu};
    svGetLogicArrElem1VecVal(&out, h, i);
    EXPECT_TRUE(LogicEq(out, data[i]));
  }
}

// C2: indexing uses the actual argument's original SystemVerilog range, here a
// descending [3:1]. The element at the left bound (index 3) occupies storage
// position 0 and positions advance toward the right bound (index 1 -> position
// 2), so the declared coordinates - not a zero-based count - select the slot.
TEST(ElementCanonicalAccess, BitDescendingOriginalRangeIndexing) {
  const SvOpenArrayDimRange ranges[] = {{7, 0}, {3, 1}};
  svBitVecVal data[3] = {0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  svBitVecVal v3 = 0x11u, v2 = 0x22u, v1 = 0x33u;
  svPutBitArrElem1VecVal(h, &v3, 3);
  svPutBitArrElem1VecVal(h, &v2, 2);
  svPutBitArrElem1VecVal(h, &v1, 1);

  // Left bound 3 -> position 0, 2 -> position 1, right bound 1 -> position 2.
  EXPECT_EQ(data[0], 0x11u);
  EXPECT_EQ(data[1], 0x22u);
  EXPECT_EQ(data[2], 0x33u);

  // And Get reads back through the same original-range coordinates.
  svBitVecVal out = 0;
  svGetBitArrElem1VecVal(&out, h, 1);
  EXPECT_EQ(out, 0x33u);
}

// C1/C3: a logic element wider than 32 bits spans two canonical words; the copy
// moves both words in full, including their bval (x/z) lanes. The handle
// models: logic [39:0] arr [0:1].
TEST(ElementCanonicalAccess, LogicMultiWordPutGetRoundTrip) {
  const SvOpenArrayDimRange ranges[] = {{39, 0}, {0, 1}};
  svLogicVecVal data[4] = {{0, 0}, {0, 0}, {0, 0}, {0, 0}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  // Two-word source: word 1 carries x/z bits in its bval lane.
  svLogicVecVal in[2] = {{0xDEADBEEFu, 0u}, {0x000000FFu, 0x0000000Fu}};
  svPutLogicArrElem1VecVal(h, in, 1);

  // Element 1 occupies storage words [2] and [3]; element 0 stays clear.
  EXPECT_TRUE(LogicEq(data[2], in[0]));
  EXPECT_TRUE(LogicEq(data[3], in[1]));
  EXPECT_TRUE(LogicEq(data[0], svLogicVecVal{0, 0}));
  EXPECT_TRUE(LogicEq(data[1], svLogicVecVal{0, 0}));

  svLogicVecVal out[2] = {{0, 0}, {0, 0}};
  svGetLogicArrElem1VecVal(out, h, 1);
  EXPECT_TRUE(LogicEq(out[0], in[0]));
  EXPECT_TRUE(LogicEq(out[1], in[1]));
}

// C3: two unpacked indices select the element row-major over the unpacked
// dimensions. The handle models: bit [3:0] arr [0:1][0:2], so index (i,j) maps
// to storage position i*3 + j.
TEST(ElementCanonicalAccess, BitTwoDimensionRowMajor) {
  const SvOpenArrayDimRange ranges[] = {{3, 0}, {0, 1}, {0, 2}};
  svBitVecVal data[6] = {0, 0, 0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 3, &desc);

  svBitVecVal a = 0x5u, b = 0xCu;
  svPutBitArrElem2VecVal(h, &a, 0, 1);  // 0*3 + 1 = 1
  svPutBitArrElem2VecVal(h, &b, 1, 2);  // 1*3 + 2 = 5

  EXPECT_EQ(data[1], 0x5u);
  EXPECT_EQ(data[5], 0xCu);

  svBitVecVal out = 0;
  svGetBitArrElem2VecVal(&out, h, 1, 2);
  EXPECT_EQ(out, 0xCu);
}

// C3: three unpacked indices select row-major over all three unpacked
// dimensions. The handle models: logic [3:0] arr [0:1][0:1][0:1], so index
// (i,j,k) maps to ((i*2 + j)*2 + k).
TEST(ElementCanonicalAccess, LogicThreeDimensionRowMajor) {
  const SvOpenArrayDimRange ranges[] = {{3, 0}, {0, 1}, {0, 1}, {0, 1}};
  svLogicVecVal data[8];
  for (auto& w : data) w = svLogicVecVal{0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 4, &desc);

  svLogicVecVal in = {0x9u, 0x6u};
  svPutLogicArrElem3VecVal(h, &in, 1, 0, 1);  // ((1*2+0)*2+1) = 5

  EXPECT_TRUE(LogicEq(data[5], in));
  EXPECT_TRUE(LogicEq(data[4], svLogicVecVal{0, 0}));

  svLogicVecVal out = {0, 0};
  svGetLogicArrElem3VecVal(&out, h, 1, 0, 1);
  EXPECT_TRUE(LogicEq(out, in));
}

// An out-of-range index or a null handle resolves no element, so the copy is a
// no-op in either direction and leaves both operands untouched - matching the
// handle/index guard the production helpers apply before touching storage.
TEST(ElementCanonicalAccess, OutOfRangeAndNullHandleAreNoOps) {
  const SvOpenArrayDimRange ranges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  // Put at an index past the [0:3] range leaves storage untouched.
  svBitVecVal in = 0xFFu;
  svPutBitArrElem1VecVal(h, &in, 4);
  for (svBitVecVal w : data) EXPECT_EQ(w, 0u);

  // Get from an out-of-range index leaves the destination untouched.
  svBitVecVal out = 0x77u;
  svGetBitArrElem1VecVal(&out, h, 4);
  EXPECT_EQ(out, 0x77u);

  // A null handle is a no-op in both directions.
  svPutBitArrElem1VecVal(nullptr, &in, 0);
  out = 0x55u;
  svGetBitArrElem1VecVal(&out, nullptr, 0);
  EXPECT_EQ(out, 0x55u);
}

// C3: the bit three-index entry points select the element row-major over three
// unpacked dimensions, mirroring the logic case but through the distinct bit
// functions. The handle models: bit [3:0] arr [0:1][0:1][0:1], so index (i,j,k)
// maps to ((i*2 + j)*2 + k).
TEST(ElementCanonicalAccess, BitThreeDimensionRowMajor) {
  const SvOpenArrayDimRange ranges[] = {{3, 0}, {0, 1}, {0, 1}, {0, 1}};
  svBitVecVal data[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 4, &desc);

  svBitVecVal in = 0xBu;
  svPutBitArrElem3VecVal(h, &in, 1, 1, 0);  // ((1*2+1)*2+0) = 6

  EXPECT_EQ(data[6], 0xBu);
  EXPECT_EQ(data[5], 0u);
  EXPECT_EQ(data[7], 0u);

  svBitVecVal out = 0;
  svGetBitArrElem3VecVal(&out, h, 1, 1, 0);
  EXPECT_EQ(out, 0xBu);
}

// C3: the logic two-index entry points select the element row-major over two
// unpacked dimensions and carry both aval/bval lanes. The handle models:
// logic [3:0] arr [0:1][0:2], so index (i,j) maps to i*3 + j.
TEST(ElementCanonicalAccess, LogicTwoDimensionRowMajor) {
  const SvOpenArrayDimRange ranges[] = {{3, 0}, {0, 1}, {0, 2}};
  svLogicVecVal data[6];
  for (auto& w : data) w = svLogicVecVal{0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 3, &desc);

  svLogicVecVal in = {0xAu, 0x5u};
  svPutLogicArrElem2VecVal(h, &in, 1, 2);  // 1*3 + 2 = 5

  EXPECT_TRUE(LogicEq(data[5], in));
  EXPECT_TRUE(LogicEq(data[4], svLogicVecVal{0, 0}));

  svLogicVecVal out = {0, 0};
  svGetLogicArrElem2VecVal(&out, h, 1, 2);
  EXPECT_TRUE(LogicEq(out, in));
}

// C2 edge: an ascending unpacked range that does not start at zero. The element
// at the left bound (index 2) occupies storage position 0 and positions advance
// toward the right bound, so the declared coordinates - not a zero-based count
// - select the slot. The handle models: bit [7:0] arr [2:5].
TEST(ElementCanonicalAccess, AscendingOffsetRangeIndexing) {
  const SvOpenArrayDimRange ranges[] = {{7, 0}, {2, 5}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  svBitVecVal v2 = 0x11u, v3 = 0x22u, v4 = 0x33u, v5 = 0x44u;
  svPutBitArrElem1VecVal(h, &v2, 2);
  svPutBitArrElem1VecVal(h, &v3, 3);
  svPutBitArrElem1VecVal(h, &v4, 4);
  svPutBitArrElem1VecVal(h, &v5, 5);

  // Left bound 2 -> position 0 ... right bound 5 -> position 3.
  EXPECT_EQ(data[0], 0x11u);
  EXPECT_EQ(data[1], 0x22u);
  EXPECT_EQ(data[2], 0x33u);
  EXPECT_EQ(data[3], 0x44u);

  svBitVecVal out = 0;
  svGetBitArrElem1VecVal(&out, h, 4);
  EXPECT_EQ(out, 0x33u);
}

// C2 edge: a descending unpacked range with negative bounds. Indexing still
// uses the actual argument's original coordinates - the left bound (index -1)
// is position 0 and the right bound (index -4) is position 3. The handle
// models: logic [7:0] arr [-1:-4].
TEST(ElementCanonicalAccess, NegativeBoundRangeIndexing) {
  const SvOpenArrayDimRange ranges[] = {{7, 0}, {-1, -4}};
  svLogicVecVal data[4];
  for (auto& w : data) w = svLogicVecVal{0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  svLogicVecVal at_left = {0x7u, 0x0u};
  svLogicVecVal at_right = {0x1u, 0x8u};
  svPutLogicArrElem1VecVal(h, &at_left, -1);
  svPutLogicArrElem1VecVal(h, &at_right, -4);

  EXPECT_TRUE(LogicEq(data[0], at_left));
  EXPECT_TRUE(LogicEq(data[3], at_right));

  svLogicVecVal out = {0, 0};
  svGetLogicArrElem1VecVal(&out, h, -4);
  EXPECT_TRUE(LogicEq(out, at_right));
}

// Guard edge: in a multidimensional handle, a single out-of-range index along
// any dimension - even when the other indices are valid - resolves no element,
// so the copy is a no-op in both directions. The handle models:
// bit [3:0] arr [0:1][0:2].
TEST(ElementCanonicalAccess, PartialOutOfRangeIndexInMultiDimIsNoOp) {
  const SvOpenArrayDimRange ranges[] = {{3, 0}, {0, 1}, {0, 2}};
  svBitVecVal data[6] = {1, 2, 3, 4, 5, 6};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 3, &desc);

  // Second index 3 is past [0:2]; storage is left untouched.
  svBitVecVal in = 0xFu;
  svPutBitArrElem2VecVal(h, &in, 1, 3);
  const svBitVecVal expected[6] = {1, 2, 3, 4, 5, 6};
  for (int i = 0; i < 6; ++i) EXPECT_EQ(data[i], expected[i]);

  // First index 2 is past [0:1]; the Get destination is left untouched.
  svBitVecVal out = 0x99u;
  svGetBitArrElem2VecVal(&out, h, 2, 0);
  EXPECT_EQ(out, 0x99u);
}

// C1/C3 edge: a packed element exactly one canonical word wide (32 bits)
// round-trips through a single full word - exercising the per-element
// word-count boundary where the width is an exact multiple of 32. The handle
// models: bit [31:0] arr [0:1].
TEST(ElementCanonicalAccess, ExactWordWidthElementRoundTrip) {
  const SvOpenArrayDimRange ranges[] = {{31, 0}, {0, 1}};
  svBitVecVal data[2] = {0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  svBitVecVal in = 0xFFFFFFFFu;
  svPutBitArrElem1VecVal(h, &in, 1);

  EXPECT_EQ(data[1], 0xFFFFFFFFu);
  EXPECT_EQ(data[0], 0u);  // a single word per element, no spill into element 0

  svBitVecVal out = 0;
  svGetBitArrElem1VecVal(&out, h, 1);
  EXPECT_EQ(out, 0xFFFFFFFFu);
}

}  // namespace
