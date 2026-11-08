#include <gtest/gtest.h>

#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

namespace {

svOpenArrayHandle MakeHandle(void* data, const SvOpenArrayDimRange* ranges,
                             int n_dims, SvOpenArrayDesc* desc) {
  desc->data = data;
  desc->n_dims = n_dims;
  desc->has_packed_part = 1;
  desc->ranges = ranges;
  return desc;
}

bool LogicEq(const svLogicVecVal& a, const svLogicVecVal& b) {
  return a.aval == b.aval && a.bval == b.bval;
}

TEST(ElementCanonicalAccess, BitPutGetRoundTrip) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svBitVecVal in = 0xA5u;
  svPutBitArrElem1VecVal(h, &in, 2);

  EXPECT_EQ(data[2], 0xA5u);
  EXPECT_EQ(data[0], 0u);
  EXPECT_EQ(data[1], 0u);
  EXPECT_EQ(data[3], 0u);

  svBitVecVal out = 0;
  svGetBitArrElem1VecVal(&out, h, 2);
  EXPECT_EQ(out, 0xA5u);
}

TEST(ElementCanonicalAccess, GetReadsPreSeededStorage) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  svLogicVecVal data[4] = {
      {0x10u, 0x01u}, {0x20u, 0x02u}, {0x30u, 0x03u}, {0x40u, 0x04u}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  for (int i = 0; i < 4; ++i) {
    svLogicVecVal out = {0xFFFFFFFFu, 0xFFFFFFFFu};
    svGetLogicArrElem1VecVal(&out, h, i);
    EXPECT_TRUE(LogicEq(out, data[i]));
  }
}

TEST(ElementCanonicalAccess, BitDescendingOriginalRangeIndexing) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {3, 1}};
  svBitVecVal data[3] = {0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svBitVecVal v3 = 0x11u, v2 = 0x22u, v1 = 0x33u;
  svPutBitArrElem1VecVal(h, &v3, 3);
  svPutBitArrElem1VecVal(h, &v2, 2);
  svPutBitArrElem1VecVal(h, &v1, 1);

  EXPECT_EQ(data[0], 0x11u);
  EXPECT_EQ(data[1], 0x22u);
  EXPECT_EQ(data[2], 0x33u);

  svBitVecVal out = 0;
  svGetBitArrElem1VecVal(&out, h, 1);
  EXPECT_EQ(out, 0x33u);
}

TEST(ElementCanonicalAccess, LogicMultiWordPutGetRoundTrip) {
  const SvOpenArrayDimRange kRanges[] = {{39, 0}, {0, 1}};
  svLogicVecVal data[4] = {{0, 0}, {0, 0}, {0, 0}, {0, 0}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svLogicVecVal in[2] = {{0xDEADBEEFu, 0u}, {0x000000FFu, 0x0000000Fu}};
  svPutLogicArrElem1VecVal(h, in, 1);

  EXPECT_TRUE(LogicEq(data[2], in[0]));
  EXPECT_TRUE(LogicEq(data[3], in[1]));
  EXPECT_TRUE(LogicEq(data[0], svLogicVecVal{0, 0}));
  EXPECT_TRUE(LogicEq(data[1], svLogicVecVal{0, 0}));

  svLogicVecVal out[2] = {{0, 0}, {0, 0}};
  svGetLogicArrElem1VecVal(out, h, 1);
  EXPECT_TRUE(LogicEq(out[0], in[0]));
  EXPECT_TRUE(LogicEq(out[1], in[1]));
}

TEST(ElementCanonicalAccess, BitTwoDimensionRowMajor) {
  const SvOpenArrayDimRange kRanges[] = {{3, 0}, {0, 1}, {0, 2}};
  svBitVecVal data[6] = {0, 0, 0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 3, &desc);

  svBitVecVal a = 0x5u, b = 0xCu;
  svPutBitArrElem2VecVal(h, &a, 0, 1);
  svPutBitArrElem2VecVal(h, &b, 1, 2);

  EXPECT_EQ(data[1], 0x5u);
  EXPECT_EQ(data[5], 0xCu);

  svBitVecVal out = 0;
  svGetBitArrElem2VecVal(&out, h, 1, 2);
  EXPECT_EQ(out, 0xCu);
}

TEST(ElementCanonicalAccess, LogicThreeDimensionRowMajor) {
  const SvOpenArrayDimRange kRanges[] = {{3, 0}, {0, 1}, {0, 1}, {0, 1}};
  svLogicVecVal data[8];
  for (auto& w : data) w = svLogicVecVal{0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 4, &desc);

  svLogicVecVal in = {0x9u, 0x6u};
  svPutLogicArrElem3VecVal(h, &in, 1, 0, 1);

  EXPECT_TRUE(LogicEq(data[5], in));
  EXPECT_TRUE(LogicEq(data[4], svLogicVecVal{0, 0}));

  svLogicVecVal out = {0, 0};
  svGetLogicArrElem3VecVal(&out, h, 1, 0, 1);
  EXPECT_TRUE(LogicEq(out, in));
}

TEST(ElementCanonicalAccess, OutOfRangeAndNullHandleAreNoOps) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svBitVecVal in = 0xFFu;
  svPutBitArrElem1VecVal(h, &in, 4);
  for (svBitVecVal w : data) EXPECT_EQ(w, 0u);

  svBitVecVal out = 0x77u;
  svGetBitArrElem1VecVal(&out, h, 4);
  EXPECT_EQ(out, 0x77u);

  svPutBitArrElem1VecVal(nullptr, &in, 0);
  out = 0x55u;
  svGetBitArrElem1VecVal(&out, nullptr, 0);
  EXPECT_EQ(out, 0x55u);
}

TEST(ElementCanonicalAccess, BitThreeDimensionRowMajor) {
  const SvOpenArrayDimRange kRanges[] = {{3, 0}, {0, 1}, {0, 1}, {0, 1}};
  svBitVecVal data[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 4, &desc);

  svBitVecVal in = 0xBu;
  svPutBitArrElem3VecVal(h, &in, 1, 1, 0);

  EXPECT_EQ(data[6], 0xBu);
  EXPECT_EQ(data[5], 0u);
  EXPECT_EQ(data[7], 0u);

  svBitVecVal out = 0;
  svGetBitArrElem3VecVal(&out, h, 1, 1, 0);
  EXPECT_EQ(out, 0xBu);
}

TEST(ElementCanonicalAccess, LogicTwoDimensionRowMajor) {
  const SvOpenArrayDimRange kRanges[] = {{3, 0}, {0, 1}, {0, 2}};
  svLogicVecVal data[6];
  for (auto& w : data) w = svLogicVecVal{0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 3, &desc);

  svLogicVecVal in = {0xAu, 0x5u};
  svPutLogicArrElem2VecVal(h, &in, 1, 2);

  EXPECT_TRUE(LogicEq(data[5], in));
  EXPECT_TRUE(LogicEq(data[4], svLogicVecVal{0, 0}));

  svLogicVecVal out = {0, 0};
  svGetLogicArrElem2VecVal(&out, h, 1, 2);
  EXPECT_TRUE(LogicEq(out, in));
}

TEST(ElementCanonicalAccess, AscendingOffsetRangeIndexing) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {2, 5}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svBitVecVal v2 = 0x11u, v3 = 0x22u, v4 = 0x33u, v5 = 0x44u;
  svPutBitArrElem1VecVal(h, &v2, 2);
  svPutBitArrElem1VecVal(h, &v3, 3);
  svPutBitArrElem1VecVal(h, &v4, 4);
  svPutBitArrElem1VecVal(h, &v5, 5);

  EXPECT_EQ(data[0], 0x11u);
  EXPECT_EQ(data[1], 0x22u);
  EXPECT_EQ(data[2], 0x33u);
  EXPECT_EQ(data[3], 0x44u);

  svBitVecVal out = 0;
  svGetBitArrElem1VecVal(&out, h, 4);
  EXPECT_EQ(out, 0x33u);
}

TEST(ElementCanonicalAccess, NegativeBoundRangeIndexing) {
  const SvOpenArrayDimRange kRanges[] = {{7, 0}, {-1, -4}};
  svLogicVecVal data[4];
  for (auto& w : data) w = svLogicVecVal{0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

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

TEST(ElementCanonicalAccess, PartialOutOfRangeIndexInMultiDimIsNoOp) {
  const SvOpenArrayDimRange kRanges[] = {{3, 0}, {0, 1}, {0, 2}};
  svBitVecVal data[6] = {1, 2, 3, 4, 5, 6};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 3, &desc);

  svBitVecVal in = 0xFu;
  svPutBitArrElem2VecVal(h, &in, 1, 3);
  const svBitVecVal kExpected[6] = {1, 2, 3, 4, 5, 6};
  for (int i = 0; i < 6; ++i) EXPECT_EQ(data[i], kExpected[i]);

  svBitVecVal out = 0x99u;
  svGetBitArrElem2VecVal(&out, h, 2, 0);
  EXPECT_EQ(out, 0x99u);
}

TEST(ElementCanonicalAccess, ExactWordWidthElementRoundTrip) {
  const SvOpenArrayDimRange kRanges[] = {{31, 0}, {0, 1}};
  svBitVecVal data[2] = {0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svBitVecVal in = 0xFFFFFFFFu;
  svPutBitArrElem1VecVal(h, &in, 1);

  EXPECT_EQ(data[1], 0xFFFFFFFFu);
  EXPECT_EQ(data[0], 0u);

  svBitVecVal out = 0;
  svGetBitArrElem1VecVal(&out, h, 1);
  EXPECT_EQ(out, 0xFFFFFFFFu);
}

TEST(ElementCanonicalAccess, TheVariadicFormsTakeAsManyIndicesAsDimensions) {
  const SvOpenArrayDimRange kBitRanges[] = {{3, 0}, {0, 1}, {0, 2}};
  svBitVecVal bits[6] = {0, 0, 0, 0, 0, 0};
  SvOpenArrayDesc bit_desc;
  svOpenArrayHandle hb = MakeHandle(bits, kBitRanges, 3, &bit_desc);
  const svBitVecVal kIn = 0xAu;
  svPutBitArrElemVecVal(hb, &kIn, 1, 2);
  EXPECT_EQ(bits[5], 0xAu);
  EXPECT_EQ(bits[4], 0u);
  svBitVecVal out = 0;
  svGetBitArrElemVecVal(&out, hb, 1, 2);
  EXPECT_EQ(out, 0xAu);
  svGetBitArrElem2VecVal(&out, hb, 1, 2);
  EXPECT_EQ(out, 0xAu);

  const SvOpenArrayDimRange kLogicRanges[] = {{3, 0}, {0, 1}, {0, 1}, {0, 1}};
  svLogicVecVal logics[8];
  for (auto& w : logics) w = svLogicVecVal{0, 0};
  SvOpenArrayDesc logic_desc;
  svOpenArrayHandle hl = MakeHandle(logics, kLogicRanges, 4, &logic_desc);
  const svLogicVecVal kLogicIn = {0x3u, 0x5u};
  svPutLogicArrElemVecVal(hl, &kLogicIn, 0, 1, 1);
  EXPECT_TRUE(LogicEq(logics[3], kLogicIn));
  svLogicVecVal logic_out = {0, 0};
  svGetLogicArrElemVecVal(&logic_out, hl, 0, 1, 1);
  EXPECT_TRUE(LogicEq(logic_out, kLogicIn));
  svGetLogicArrElem3VecVal(&logic_out, hl, 0, 1, 1);
  EXPECT_TRUE(LogicEq(logic_out, kLogicIn));
  const SvOpenArrayDimRange kVectorAlone[] = {{3, 0}};
  svBitVecVal vector[1] = {0};
  SvOpenArrayDesc vector_desc;
  svOpenArrayHandle hv = MakeHandle(vector, kVectorAlone, 1, &vector_desc);
  svPutBitArrElemVecVal(hv, &kIn, 0);
  EXPECT_EQ(vector[0], 0u);
}

}  // namespace
