#include <gtest/gtest.h>

#include <type_traits>

#include "parser/ast_type.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_open_array.h"

using namespace delta;

namespace {

svOpenArrayHandle MakeHandle(void* data, const SvOpenArrayDimRange* ranges,
                             int n_dims, SvOpenArrayDesc* desc) {
  desc->data = data;
  desc->n_dims = n_dims;
  desc->has_packed_part = 1;
  desc->ranges = ranges;
  return desc;
}

TEST(ScalarElementAccess, BitPutGetRoundTrip) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 3}};
  svBitVecVal data[4] = {0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svPutBitArrElem1(h, 1, 2);

  EXPECT_EQ(data[2] & 1u, 1u);
  EXPECT_EQ(data[0] & 1u, 0u);
  EXPECT_EQ(data[1] & 1u, 0u);
  EXPECT_EQ(data[3] & 1u, 0u);

  EXPECT_EQ(svGetBitArrElem1(h, 2), 1);
  EXPECT_EQ(svGetBitArrElem1(h, 0), 0);
}

TEST(ScalarElementAccess, LogicFourStateRoundTrip) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 3}};
  svLogicVecVal data[4] = {{0, 0}, {0, 0}, {0, 0}, {0, 0}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  const svLogic kValues[4] = {sv_0, sv_1, sv_z, sv_x};
  for (int i = 0; i < 4; ++i) svPutLogicArrElem1(h, kValues[i], i);

  for (int i = 0; i < 4; ++i) EXPECT_EQ(svGetLogicArrElem1(h, i), kValues[i]);
}

TEST(ScalarElementAccess, LogicPutUsesCanonicalEncoding) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 1}};
  svLogicVecVal data[2] = {{0, 0}, {0, 0}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svPutLogicArrElem1(h, sv_z, 0);
  EXPECT_EQ(data[0].aval & 1u, 0u);
  EXPECT_EQ(data[0].bval & 1u, 1u);

  svPutLogicArrElem1(h, sv_x, 1);
  EXPECT_EQ(data[1].aval & 1u, 1u);
  EXPECT_EQ(data[1].bval & 1u, 1u);
}

TEST(ScalarElementAccess, BitGetReadsOnlyBitZero) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 1}};
  svBitVecVal data[2] = {0xFFFFFFFEu, 0x00000001u};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  EXPECT_EQ(svGetBitArrElem1(h, 0), 0);
  EXPECT_EQ(svGetBitArrElem1(h, 1), 1);
}

TEST(ScalarElementAccess, BitPutTouchesOnlyBitZero) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 1}};
  svBitVecVal data[2] = {0xFFFFFFF0u, 0x0000000Fu};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svPutBitArrElem1(h, 1, 0);
  EXPECT_EQ(data[0], 0xFFFFFFF1u);

  svPutBitArrElem1(h, 0, 1);
  EXPECT_EQ(data[1], 0x0000000Eu);
}

TEST(ScalarElementAccess, LogicGetReadsOnlyBitZero) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 3}};
  svLogicVecVal data[4] = {{0xFFFFFFFEu, 0xFFFFFFFEu},
                           {0x00000001u, 0x00000000u},
                           {0xFFFFFFFEu, 0x00000001u},
                           {0xFFFFFFFFu, 0xFFFFFFFFu}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  EXPECT_EQ(svGetLogicArrElem1(h, 0), sv_0);
  EXPECT_EQ(svGetLogicArrElem1(h, 1), sv_1);
  EXPECT_EQ(svGetLogicArrElem1(h, 2), sv_z);
  EXPECT_EQ(svGetLogicArrElem1(h, 3), sv_x);
}

TEST(ScalarElementAccess, LogicPutTouchesOnlyBitZero) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 1}};
  svLogicVecVal data[2] = {{0xAAAAAAAAu, 0x55555555u},
                           {0xFFFFFFFFu, 0x00000000u}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svPutLogicArrElem1(h, sv_1, 0);
  EXPECT_EQ(data[0].aval, 0xAAAAAAABu);
  EXPECT_EQ(data[0].bval, 0x55555554u);

  svPutLogicArrElem1(h, sv_z, 1);
  EXPECT_EQ(data[1].aval, 0xFFFFFFFEu);
  EXPECT_EQ(data[1].bval, 0x00000001u);
}

TEST(ScalarElementAccess, BitDescendingOriginalRangeIndexing) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {3, 1}};
  svBitVecVal data[3] = {0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svPutBitArrElem1(h, 1, 3);
  svPutBitArrElem1(h, 0, 2);
  svPutBitArrElem1(h, 1, 1);

  EXPECT_EQ(data[0] & 1u, 1u);
  EXPECT_EQ(data[1] & 1u, 0u);
  EXPECT_EQ(data[2] & 1u, 1u);

  EXPECT_EQ(svGetBitArrElem1(h, 1), 1);
}

TEST(ScalarElementAccess, LogicNegativeBoundRangeIndexing) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {-1, -4}};
  svLogicVecVal data[4] = {{0, 0}, {0, 0}, {0, 0}, {0, 0}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svPutLogicArrElem1(h, sv_1, -1);
  svPutLogicArrElem1(h, sv_z, -4);

  EXPECT_EQ(svGetLogicArrElem1(h, -1), sv_1);
  EXPECT_EQ(svGetLogicArrElem1(h, -4), sv_z);
  EXPECT_EQ(svGetLogicArrElem1(h, -2), sv_0);
}

TEST(ScalarElementAccess, BitTwoDimensionRowMajor) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 1}, {0, 2}};
  svBitVecVal data[6] = {0, 0, 0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 3, &desc);

  svPutBitArrElem2(h, 1, 0, 1);
  svPutBitArrElem2(h, 1, 1, 2);

  EXPECT_EQ(data[1] & 1u, 1u);
  EXPECT_EQ(data[5] & 1u, 1u);
  EXPECT_EQ(svGetBitArrElem2(h, 1, 2), 1);
  EXPECT_EQ(svGetBitArrElem2(h, 0, 0), 0);
}

TEST(ScalarElementAccess, LogicThreeDimensionRowMajor) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 1}, {0, 1}, {0, 1}};
  svLogicVecVal data[8];
  for (auto& w : data) w = svLogicVecVal{0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 4, &desc);

  svPutLogicArrElem3(h, sv_x, 1, 0, 1);

  EXPECT_EQ(svGetLogicArrElem3(h, 1, 0, 1), sv_x);
  EXPECT_EQ(svGetLogicArrElem3(h, 1, 0, 0), sv_0);
}

TEST(ScalarElementAccess, BitThreeDimensionRowMajor) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 1}, {0, 1}, {0, 1}};
  svBitVecVal data[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 4, &desc);

  svPutBitArrElem3(h, 1, 1, 1, 0);

  EXPECT_EQ(data[6] & 1u, 1u);
  EXPECT_EQ(svGetBitArrElem3(h, 1, 1, 0), 1);
  EXPECT_EQ(svGetBitArrElem3(h, 0, 0, 0), 0);
}

TEST(ScalarElementAccess, LogicTwoDimensionRowMajor) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 1}, {0, 2}};
  svLogicVecVal data[6];
  for (auto& w : data) w = svLogicVecVal{0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 3, &desc);

  svPutLogicArrElem2(h, sv_z, 1, 2);

  EXPECT_EQ(svGetLogicArrElem2(h, 1, 2), sv_z);
  EXPECT_EQ(svGetLogicArrElem2(h, 0, 0), sv_0);
}

TEST(ScalarElementAccess, BitVariadicMatchesNumbered) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 1}, {0, 2}};
  svBitVecVal data[6] = {0, 0, 0, 0, 0, 0};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 3, &desc);

  svPutBitArrElem(h, 1, 1, 2);
  EXPECT_EQ(data[5] & 1u, 1u);
  EXPECT_EQ(svGetBitArrElem2(h, 1, 2), 1);
  EXPECT_EQ(svGetBitArrElem(h, 1, 2), 1);
}

TEST(ScalarElementAccess, LogicVariadicMatchesNumbered) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 3}};
  svLogicVecVal data[4] = {{0, 0}, {0, 0}, {0, 0}, {0, 0}};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svPutLogicArrElem(h, sv_z, 2);
  EXPECT_EQ(svGetLogicArrElem1(h, 2), sv_z);
  EXPECT_EQ(svGetLogicArrElem(h, 2), sv_z);
}

TEST(ScalarElementAccess, VariadicNoUnpackedDimensionsIsNoOp) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}};
  svBitVecVal bit_data[1] = {1};
  svLogicVecVal logic_data[1] = {{1, 1}};
  SvOpenArrayDesc bit_desc;
  SvOpenArrayDesc logic_desc;
  svOpenArrayHandle bh = MakeHandle(bit_data, kRanges, 1, &bit_desc);
  svOpenArrayHandle lh = MakeHandle(logic_data, kRanges, 1, &logic_desc);

  EXPECT_EQ(svGetBitArrElem(bh, 0), 0);
  EXPECT_EQ(svGetLogicArrElem(lh, 0), 0);

  svPutBitArrElem(bh, 0, 0);
  svPutLogicArrElem(lh, sv_0, 0);
  EXPECT_EQ(bit_data[0], 1u);
  EXPECT_EQ(logic_data[0].aval, 1u);
  EXPECT_EQ(logic_data[0].bval, 1u);
}

TEST(ScalarElementAccess, OutOfRangeAndNullHandle) {
  const SvOpenArrayDimRange kRanges[] = {{0, 0}, {0, 3}};
  svBitVecVal data[4] = {1, 1, 1, 1};
  SvOpenArrayDesc desc;
  svOpenArrayHandle h = MakeHandle(data, kRanges, 2, &desc);

  svPutBitArrElem1(h, 0, 4);
  for (svBitVecVal w : data) EXPECT_EQ(w & 1u, 1u);

  EXPECT_EQ(svGetBitArrElem1(h, 4), 0);
  EXPECT_EQ(svGetBitArrElem1(nullptr, 0), 0);
  EXPECT_EQ(svGetLogicArrElem1(nullptr, 0), 0);

  svPutBitArrElem1(nullptr, 1, 0);
  svPutLogicArrElem1(nullptr, sv_1, 0);
}

TEST(DpiScalarElementModel, TheScalarGroupServesScalarElementsAlone) {
  EXPECT_EQ(DpiElementFunctionGroupOf(DataTypeKind::kBit, 1),
            DpiElementFunctionGroup::kScalar);
  EXPECT_EQ(DpiElementFunctionGroupOf(DataTypeKind::kLogic, 1),
            DpiElementFunctionGroup::kScalar);
  EXPECT_EQ(DpiElementFunctionGroupOf(DataTypeKind::kBit, 8),
            DpiElementFunctionGroup::kCanonical);
  EXPECT_EQ(DpiElementFunctionGroupOf(DataTypeKind::kLogic, 64),
            DpiElementFunctionGroup::kCanonical);
  EXPECT_EQ(DpiElementFunctionGroupOf(DataTypeKind::kInt, 0),
            DpiElementFunctionGroup::kAddress);
  EXPECT_EQ(DpiElementFunctionGroupOf(DataTypeKind::kStruct, 0),
            DpiElementFunctionGroup::kAddress);
}

TEST(DpiScalarElementModel, TheGroupHasAGetAndAPutForBitAndForLogic) {
  EXPECT_EQ(DpiScalarElementFunction(false, false), "svGetBitArrElem");
  EXPECT_EQ(DpiScalarElementFunction(false, true), "svPutBitArrElem");
  EXPECT_EQ(DpiScalarElementFunction(true, false), "svGetLogicArrElem");
  EXPECT_EQ(DpiScalarElementFunction(true, true), "svPutLogicArrElem");
}

TEST(DpiScalarElementModel, AGetReturnsTheScalarAndAPutTakesItByValue) {
  EXPECT_TRUE(
      (std::is_same<decltype(svGetBitArrElem1(nullptr, 0)), svBit>::value));
  EXPECT_TRUE(
      (std::is_same<decltype(svGetLogicArrElem1(nullptr, 0)), svLogic>::value));
  EXPECT_TRUE((std::is_same<decltype(&svPutBitArrElem1),
                            void (*)(svOpenArrayHandle, svBit, int)>::value));
  EXPECT_TRUE(
      (std::is_same<decltype(&svPutLogicArrElem2),
                    void (*)(svOpenArrayHandle, svLogic, int, int)>::value));
}

}  // namespace
