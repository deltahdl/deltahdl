#include <gtest/gtest.h>

#include "simulator/svdpi.h"

// Annex H.12.6 - Access to scalar elements (bit and logic).
//
// H.12.6 defines the DPI C-layer functions that read or write a single scalar
// element of an open array, i.e., when an element is a simple bit or logic
// scalar rather than a packed vector. The svGetBitArrElem*/svGetLogicArrElem*
// functions read a scalar and the svPutBitArrElem*/svPutLogicArrElem* functions
// write one, for both element types, for one, two, or three unpacked indices,
// and through a variadic form that accepts one index per unpacked dimension.
// Its declarative requirements are:
//
//   C1 - a Get reads, and a Put writes, exactly the scalar value of the
//   selected
//        element (bit 0 of that element's canonical word); a logic scalar
//        carries the full four-state value 0/1/z/x;
//   C2 - the actual argument's original SystemVerilog ranges index the open
//        array, so descending, offset, or negative unpacked ranges select by
//        their declared coordinates, not by a zero-based position;
//   C3 - multiple unpacked indices select the element row-major, and the
//        variadic form resolves the same element as the matching numbered form.
//
// These tests build an svOpenArrayHandle backed by a real svOpenArrayDesc
// buffer whose packed dimension is one bit wide (a scalar element) and observe
// the svdpi.cpp scalar access functions applying those rules.

namespace {

svOpenArrayHandle MakeHandle(void* data, const svOpenArrayDimRange* ranges,
                             int n_dims, svOpenArrayDesc* desc) {
  desc->data = data;
  desc->n_dims = n_dims;
  desc->ranges = ranges;
  return desc;
}

// C1: a Put then a Get round-trips a scalar bit through simulator storage, and
// the value lands at the storage slot the index selects. The handle models a
// scalar array: bit arr [0:3] (packed dimension one bit wide).
TEST(ScalarElementAccess, BitPutGetRoundTrip) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  svPutBitArrElem1(h, 1, 2);

  // The scalar lands at storage position 2 and the other slots stay clear.
  EXPECT_EQ(data[2] & 1u, 1u);
  EXPECT_EQ(data[0] & 1u, 0u);
  EXPECT_EQ(data[1] & 1u, 0u);
  EXPECT_EQ(data[3] & 1u, 0u);

  EXPECT_EQ(svGetBitArrElem1(h, 2), 1);
  EXPECT_EQ(svGetBitArrElem1(h, 0), 0);
}

// C1: every four-state logic value round-trips through simulator storage,
// including z and x. The handle models: logic arr [0:3].
TEST(ScalarElementAccess, LogicFourStateRoundTrip) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 3}};
  svLogicVecVal data[4] = {{0, 0}, {0, 0}, {0, 0}, {0, 0}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  const svLogic values[4] = {sv_0, sv_1, sv_z, sv_x};
  for (int i = 0; i < 4; ++i) svPutLogicArrElem1(h, values[i], i);

  for (int i = 0; i < 4; ++i) EXPECT_EQ(svGetLogicArrElem1(h, i), values[i]);
}

// C1: a Put writes the canonical aval/bval encoding into bit 0, and a Get reads
// that encoding back. The handle models: logic arr [0:1].
TEST(ScalarElementAccess, LogicPutUsesCanonicalEncoding) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 1}};
  svLogicVecVal data[2] = {{0, 0}, {0, 0}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  // z is aval bit 0 = 0, bval bit 0 = 1; x is both bits set.
  svPutLogicArrElem1(h, sv_z, 0);
  EXPECT_EQ(data[0].aval & 1u, 0u);
  EXPECT_EQ(data[0].bval & 1u, 1u);

  svPutLogicArrElem1(h, sv_x, 1);
  EXPECT_EQ(data[1].aval & 1u, 1u);
  EXPECT_EQ(data[1].bval & 1u, 1u);
}

// C1: a Get reads only bit 0 of the element's canonical word; higher bits of
// the storage word are not part of the scalar value. The handle models: bit
// arr[0:1] pre-seeded directly so the read cannot be echoing a prior Put.
TEST(ScalarElementAccess, BitGetReadsOnlyBitZero) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 1}};
  svBitVecVal data[2] = {0xFFFFFFFEu, 0x00000001u};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  // Slot 0 has bit 0 clear (despite garbage above); slot 1 has bit 0 set.
  EXPECT_EQ(svGetBitArrElem1(h, 0), 0);
  EXPECT_EQ(svGetBitArrElem1(h, 1), 1);
}

// C1: a Put touches only bit 0 of the element's word, leaving the surrounding
// bits of that storage word unchanged. The handle models: bit arr [0:1].
TEST(ScalarElementAccess, BitPutTouchesOnlyBitZero) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 1}};
  svBitVecVal data[2] = {0xFFFFFFF0u, 0x0000000Fu};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  svPutBitArrElem1(h, 1, 0);  // set bit 0, keep the high nibble pattern
  EXPECT_EQ(data[0], 0xFFFFFFF1u);

  svPutBitArrElem1(h, 0, 1);  // clear bit 0, keep the rest
  EXPECT_EQ(data[1], 0x0000000Eu);
}

// C1: a logic Get decodes only bit 0 of the element's canonical aval/bval pair;
// the higher bits of the storage word are not part of the scalar. Storage is
// pre-seeded directly so the read cannot be echoing a prior Put, with garbage
// in the upper bits to prove they are ignored. The handle models: logic arr
// [0:3].
TEST(ScalarElementAccess, LogicGetReadsOnlyBitZero) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 3}};
  svLogicVecVal data[4] = {{0xFFFFFFFEu, 0xFFFFFFFEu},   // bit0: a=0 b=0 -> 0
                           {0x00000001u, 0x00000000u},   // bit0: a=1 b=0 -> 1
                           {0xFFFFFFFEu, 0x00000001u},   // bit0: a=0 b=1 -> z
                           {0xFFFFFFFFu, 0xFFFFFFFFu}};  // bit0: a=1 b=1 -> x
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  EXPECT_EQ(svGetLogicArrElem1(h, 0), sv_0);
  EXPECT_EQ(svGetLogicArrElem1(h, 1), sv_1);
  EXPECT_EQ(svGetLogicArrElem1(h, 2), sv_z);
  EXPECT_EQ(svGetLogicArrElem1(h, 3), sv_x);
}

// C1: a logic Put updates only bit 0 of the element's aval/bval lanes, leaving
// the surrounding bits of those words unchanged. Storage is pre-seeded with a
// distinct pattern in the upper bits to prove they survive. The handle models:
// logic arr [0:1].
TEST(ScalarElementAccess, LogicPutTouchesOnlyBitZero) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 1}};
  svLogicVecVal data[2] = {{0xAAAAAAAAu, 0x55555555u},
                           {0xFFFFFFFFu, 0x00000000u}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  // sv_1 sets aval bit 0 and clears bval bit 0; the upper bits stay put.
  svPutLogicArrElem1(h, sv_1, 0);
  EXPECT_EQ(data[0].aval, 0xAAAAAAABu);
  EXPECT_EQ(data[0].bval, 0x55555554u);

  // sv_z clears aval bit 0 and sets bval bit 0; the upper bits stay put.
  svPutLogicArrElem1(h, sv_z, 1);
  EXPECT_EQ(data[1].aval, 0xFFFFFFFEu);
  EXPECT_EQ(data[1].bval, 0x00000001u);
}

// C2: indexing uses the actual argument's original SystemVerilog range, here a
// descending [3:1]. The element at the left bound (index 3) is storage position
// 0 and positions advance toward the right bound. The handle models:
// bit arr [3:1].
TEST(ScalarElementAccess, BitDescendingOriginalRangeIndexing) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {3, 1}};
  svBitVecVal data[3] = {0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  svPutBitArrElem1(h, 1, 3);  // left bound -> position 0
  svPutBitArrElem1(h, 0, 2);  // -> position 1
  svPutBitArrElem1(h, 1, 1);  // right bound -> position 2

  EXPECT_EQ(data[0] & 1u, 1u);
  EXPECT_EQ(data[1] & 1u, 0u);
  EXPECT_EQ(data[2] & 1u, 1u);

  EXPECT_EQ(svGetBitArrElem1(h, 1), 1);
}

// C2 edge: a descending unpacked range with negative bounds; the left bound
// (index -1) is position 0 and the right bound (index -4) is position 3. The
// handle models: logic arr [-1:-4].
TEST(ScalarElementAccess, LogicNegativeBoundRangeIndexing) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {-1, -4}};
  svLogicVecVal data[4] = {{0, 0}, {0, 0}, {0, 0}, {0, 0}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  svPutLogicArrElem1(h, sv_1, -1);  // left bound -> position 0
  svPutLogicArrElem1(h, sv_z, -4);  // right bound -> position 3

  EXPECT_EQ(svGetLogicArrElem1(h, -1), sv_1);
  EXPECT_EQ(svGetLogicArrElem1(h, -4), sv_z);
  EXPECT_EQ(svGetLogicArrElem1(h, -2), sv_0);
}

// C3: two unpacked indices select the element row-major. The handle models:
// bit arr [0:1][0:2], so index (i,j) maps to storage position i*3 + j.
TEST(ScalarElementAccess, BitTwoDimensionRowMajor) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 1}, {0, 2}};
  svBitVecVal data[6] = {0, 0, 0, 0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 3, &desc);

  svPutBitArrElem2(h, 1, 0, 1);  // 0*3 + 1 = 1
  svPutBitArrElem2(h, 1, 1, 2);  // 1*3 + 2 = 5

  EXPECT_EQ(data[1] & 1u, 1u);
  EXPECT_EQ(data[5] & 1u, 1u);
  EXPECT_EQ(svGetBitArrElem2(h, 1, 2), 1);
  EXPECT_EQ(svGetBitArrElem2(h, 0, 0), 0);
}

// C3: three unpacked indices select the element row-major over all three
// unpacked dimensions. The handle models: logic arr [0:1][0:1][0:1], so index
// (i,j,k) maps to ((i*2 + j)*2 + k).
TEST(ScalarElementAccess, LogicThreeDimensionRowMajor) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 1}, {0, 1}, {0, 1}};
  svLogicVecVal data[8];
  for (auto& w : data) w = svLogicVecVal{0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 4, &desc);

  svPutLogicArrElem3(h, sv_x, 1, 0, 1);  // ((1*2+0)*2+1) = 5

  EXPECT_EQ(svGetLogicArrElem3(h, 1, 0, 1), sv_x);
  EXPECT_EQ(svGetLogicArrElem3(h, 1, 0, 0), sv_0);
}

// C3: the bit three-index entry points select the element row-major over three
// unpacked dimensions, exercising the distinct
// svPutBitArrElem3/svGetBitArrElem3 functions. The handle models: bit arr
// [0:1][0:1][0:1], so index (i,j,k) maps to ((i*2 + j)*2 + k).
TEST(ScalarElementAccess, BitThreeDimensionRowMajor) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 1}, {0, 1}, {0, 1}};
  svBitVecVal data[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 4, &desc);

  svPutBitArrElem3(h, 1, 1, 1, 0);  // ((1*2+1)*2+0) = 6

  EXPECT_EQ(data[6] & 1u, 1u);
  EXPECT_EQ(svGetBitArrElem3(h, 1, 1, 0), 1);
  EXPECT_EQ(svGetBitArrElem3(h, 0, 0, 0), 0);
}

// C3: the logic two-index entry points select the element row-major over two
// unpacked dimensions and carry the four-state value, exercising the distinct
// svPutLogicArrElem2/svGetLogicArrElem2 functions. The handle models:
// logic arr [0:1][0:2], so index (i,j) maps to i*3 + j.
TEST(ScalarElementAccess, LogicTwoDimensionRowMajor) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 1}, {0, 2}};
  svLogicVecVal data[6];
  for (auto& w : data) w = svLogicVecVal{0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 3, &desc);

  svPutLogicArrElem2(h, sv_z, 1, 2);  // 1*3 + 2 = 5

  EXPECT_EQ(svGetLogicArrElem2(h, 1, 2), sv_z);
  EXPECT_EQ(svGetLogicArrElem2(h, 0, 0), sv_0);
}

// C3: the variadic forms resolve the same element as the matching numbered
// form. The handle models: bit arr [0:1][0:2] (two unpacked dimensions).
TEST(ScalarElementAccess, BitVariadicMatchesNumbered) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 1}, {0, 2}};
  svBitVecVal data[6] = {0, 0, 0, 0, 0, 0};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 3, &desc);

  // Write via the variadic form, read back via both the numbered and variadic
  // forms - both must land on storage position 1*3 + 2 = 5.
  svPutBitArrElem(h, 1, 1, 2);
  EXPECT_EQ(data[5] & 1u, 1u);
  EXPECT_EQ(svGetBitArrElem2(h, 1, 2), 1);
  EXPECT_EQ(svGetBitArrElem(h, 1, 2), 1);
}

// C3: the logic variadic forms likewise match the numbered form and carry the
// full four-state value. The handle models: logic arr [0:3] (one unpacked dim).
TEST(ScalarElementAccess, LogicVariadicMatchesNumbered) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 3}};
  svLogicVecVal data[4] = {{0, 0}, {0, 0}, {0, 0}, {0, 0}};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  svPutLogicArrElem(h, sv_z, 2);
  EXPECT_EQ(svGetLogicArrElem1(h, 2), sv_z);
  EXPECT_EQ(svGetLogicArrElem(h, 2), sv_z);
}

// C3 edge: the variadic forms supply one index per unpacked dimension. A handle
// with no unpacked dimensions (only the packed dimension) leaves them nothing
// to resolve, so a variadic Get returns the zero scalar and a variadic Put is a
// no-op. The handle models a degenerate single-packed-dimension descriptor.
TEST(ScalarElementAccess, VariadicNoUnpackedDimensionsIsNoOp) {
  const svOpenArrayDimRange ranges[] = {{0, 0}};
  svBitVecVal bit_data[1] = {1};
  svLogicVecVal logic_data[1] = {{1, 1}};
  svOpenArrayDesc bit_desc;
  svOpenArrayDesc logic_desc;
  svOpenArrayHandle bh = MakeHandle(bit_data, ranges, 1, &bit_desc);
  svOpenArrayHandle lh = MakeHandle(logic_data, ranges, 1, &logic_desc);

  // Gets resolve no element and return the zero scalar.
  EXPECT_EQ(svGetBitArrElem(bh, 0), 0);
  EXPECT_EQ(svGetLogicArrElem(lh, 0), 0);

  // Puts resolve no element and leave storage untouched.
  svPutBitArrElem(bh, 0, 0);
  svPutLogicArrElem(lh, sv_0, 0);
  EXPECT_EQ(bit_data[0], 1u);
  EXPECT_EQ(logic_data[0].aval, 1u);
  EXPECT_EQ(logic_data[0].bval, 1u);
}

// An out-of-range index or a null handle resolves no element, so a Get returns
// the zero scalar and a Put leaves storage untouched. The handle models:
// bit arr [0:3].
TEST(ScalarElementAccess, OutOfRangeAndNullHandle) {
  const svOpenArrayDimRange ranges[] = {{0, 0}, {0, 3}};
  svBitVecVal data[4] = {1, 1, 1, 1};
  svOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, ranges, 2, &desc);

  // Put past the [0:3] range leaves storage untouched.
  svPutBitArrElem1(h, 0, 4);
  for (svBitVecVal w : data) EXPECT_EQ(w & 1u, 1u);

  // Get from an out-of-range index or a null handle returns the zero scalar.
  EXPECT_EQ(svGetBitArrElem1(h, 4), 0);
  EXPECT_EQ(svGetBitArrElem1(nullptr, 0), 0);
  EXPECT_EQ(svGetLogicArrElem1(nullptr, 0), 0);

  // A null-handle Put is a no-op (no crash, nothing to observe but stability).
  svPutBitArrElem1(nullptr, 1, 0);
  svPutLogicArrElem1(nullptr, sv_1, 0);
}

}  // namespace
