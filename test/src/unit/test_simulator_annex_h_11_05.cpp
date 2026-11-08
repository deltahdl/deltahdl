#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/svdpi.h"

namespace {

TEST(SvDpi, BitSelectBit) {
  svBitVecVal bv = 0x0A;
  EXPECT_EQ(svGetBitselBit(&bv, 0), 0u);
  EXPECT_EQ(svGetBitselBit(&bv, 1), 1u);
  EXPECT_EQ(svGetBitselBit(&bv, 2), 0u);
  EXPECT_EQ(svGetBitselBit(&bv, 3), 1u);
}

TEST(SvDpi, BitSelectLogic) {
  svLogicVecVal lv;
  lv.aval = 0x03;
  lv.bval = 0x02;

  EXPECT_EQ(svGetBitselLogic(&lv, 0), sv_1);

  EXPECT_EQ(svGetBitselLogic(&lv, 1), sv_x);
}

TEST(SvDpi, PutBitSelectBit) {
  svBitVecVal bv = 0;
  svPutBitselBit(&bv, 3, 1);
  EXPECT_EQ(bv, 8u);
  svPutBitselBit(&bv, 3, 0);
  EXPECT_EQ(bv, 0u);
}

TEST(SvDpi, PutBitSelectLogic) {
  svLogicVecVal lv = {0, 0};
  svPutBitselLogic(&lv, 0, sv_1);
  EXPECT_EQ(lv.aval, 1u);
  EXPECT_EQ(lv.bval, 0u);
  svPutBitselLogic(&lv, 2, sv_z);
  EXPECT_EQ(lv.aval & (1u << 2), 0u);
  EXPECT_EQ(lv.bval & (1u << 2), 4u);
}

TEST(SvDpi, PutPartSelectBit) {
  svBitVecVal dst = 0;
  svBitVecVal src = 0x0F;
  svPutPartselBit(&dst, src, 4, 8);
  EXPECT_EQ(dst, 0xF0u);
}

TEST(SvDpi, PutPartSelectBitPreservesSurrounding) {
  svBitVecVal dst = 0xFFFFFFFFu;
  svBitVecVal src = 0x00u;
  svPutPartselBit(&dst, src, 4, 8);
  EXPECT_EQ((dst >> 4) & 0xFFu, 0u);
  EXPECT_EQ(dst & 0xFu, 0xFu);
  EXPECT_EQ(dst >> 12, 0xFFFFFu);
}

TEST(SvDpi, PutPartSelectLogicPreservesSurrounding) {
  svLogicVecVal dst;
  dst.aval = 0xFFFFFFFFu;
  dst.bval = 0x00000000u;
  svLogicVecVal src;
  src.aval = 0x00u;
  src.bval = 0x00u;
  svPutPartselLogic(&dst, src, 4, 8);
  EXPECT_EQ((dst.aval >> 4) & 0xFFu, 0u);
  EXPECT_EQ(dst.aval & 0xFu, 0xFu);
  EXPECT_EQ(dst.aval >> 12, 0xFFFFFu);
  EXPECT_EQ(dst.bval, 0u);
}

TEST(SvDpi, GetPartSelectBitPreservesHighBits) {
  svBitVecVal src = 0xABCDEF12u;
  svBitVecVal dst = 0xFFFFFFFFu;
  svGetPartselBit(&dst, &src, 4, 8);
  EXPECT_EQ(dst & 0xFFu, (src >> 4) & 0xFFu);
  EXPECT_EQ(dst >> 8, 0xFFFFFFu);
}

TEST(SvDpi, GetPartSelectLogicPreservesHighBits) {
  svLogicVecVal src;
  src.aval = 0xABCDEF12u;
  src.bval = 0x00000000u;
  svLogicVecVal dst;
  dst.aval = 0xFFFFFFFFu;
  dst.bval = 0xFFFFFFFFu;
  svGetPartselLogic(&dst, &src, 4, 8);
  EXPECT_EQ(dst.aval & 0xFFu, (src.aval >> 4) & 0xFFu);
  EXPECT_EQ(dst.bval & 0xFFu, 0u);
  EXPECT_EQ(dst.aval >> 8, 0xFFFFFFu);
  EXPECT_EQ(dst.bval >> 8, 0xFFFFFFu);
}

TEST(SvDpi, BitSelectUpperWord) {
  svBitVecVal bv[3] = {0u, 0u, 0u};
  bv[2] = 1u << 2;
  EXPECT_EQ(svGetBitselBit(bv, 66), 1u);
  EXPECT_EQ(svGetBitselBit(bv, 65), 0u);

  svPutBitselBit(bv, 33, 1);
  EXPECT_EQ(bv[1], 1u << 1);
  svPutBitselBit(bv, 66, 0);
  EXPECT_EQ(bv[2], 0u);
}

TEST(SvDpi, BitSelectLogicUpperWord) {
  svLogicVecVal lv[3] = {{0, 0}, {0, 0}, {0, 0}};
  svPutBitselLogic(lv, 34, sv_z);
  EXPECT_EQ(lv[1].aval, 0u);
  EXPECT_EQ(lv[1].bval, 1u << 2);
  EXPECT_EQ(svGetBitselLogic(lv, 34), sv_z);
}

TEST(SvDpi, GetPartSelectBitAcrossWordBoundary) {
  svBitVecVal src[2] = {0x80000000u, 0x0000000Fu};
  svBitVecVal dst = 0xFFFFFFFFu;
  svGetPartselBit(&dst, src, 28, 8);
  EXPECT_EQ(dst & 0xFFu, 0xF8u);
  EXPECT_EQ(dst >> 8, 0xFFFFFFu);
}

TEST(SvDpi, GetPartSelectLogicAcrossWordBoundary) {
  svLogicVecVal src[2] = {{0x80000000u, 0u}, {0x0000000Fu, 0u}};
  svLogicVecVal dst = {0xFFFFFFFFu, 0xFFFFFFFFu};
  svGetPartselLogic(&dst, src, 28, 8);
  EXPECT_EQ(dst.aval & 0xFFu, 0xF8u);
  EXPECT_EQ(dst.bval & 0xFFu, 0u);
  EXPECT_EQ(dst.aval >> 8, 0xFFFFFFu);
  EXPECT_EQ(dst.bval >> 8, 0xFFFFFFu);
}

TEST(SvDpi, PutPartSelectBitAcrossWordBoundary) {
  svBitVecVal dst[2] = {0x0FFFFFFFu, 0xFFFFFFF0u};
  svPutPartselBit(dst, 0xFFu, 28, 8);
  EXPECT_EQ(dst[0], 0xFFFFFFFFu);
  EXPECT_EQ(dst[1], 0xFFFFFFFFu);
}

TEST(SvDpi, PutPartSelectLogicAcrossWordBoundary) {
  svLogicVecVal dst[2] = {{0u, 0u}, {0u, 0u}};
  svLogicVecVal src = {0xFFu, 0x00u};
  svPutPartselLogic(dst, src, 28, 8);
  EXPECT_EQ(dst[0].aval, 0xF0000000u);
  EXPECT_EQ(dst[1].aval, 0x0000000Fu);
  EXPECT_EQ(dst[0].bval, 0u);
  EXPECT_EQ(dst[1].bval, 0u);
}

TEST(SvDpi, PartSelectFullWidthWord) {
  svBitVecVal src = 0xDEADBEEFu;
  svBitVecVal getdst = 0x12345678u;
  svGetPartselBit(&getdst, &src, 0, 32);
  EXPECT_EQ(getdst, 0xDEADBEEFu);

  svBitVecVal putdst = 0u;
  svPutPartselBit(&putdst, 0xDEADBEEFu, 0, 32);
  EXPECT_EQ(putdst, 0xDEADBEEFu);
}

TEST(SvDpi, PartSelectWidthOutOfRangeIsNoOp) {
  svBitVecVal src = 0xFFFFFFFFu;
  svBitVecVal getdst = 0x12345678u;
  svGetPartselBit(&getdst, &src, 0, 33);
  EXPECT_EQ(getdst, 0x12345678u);
  svGetPartselBit(&getdst, &src, 0, 0);
  EXPECT_EQ(getdst, 0x12345678u);

  svBitVecVal putdst = 0x12345678u;
  svPutPartselBit(&putdst, 0xFFu, 0, 33);
  EXPECT_EQ(putdst, 0x12345678u);
  svPutPartselBit(&putdst, 0xFFu, 0, 0);
  EXPECT_EQ(putdst, 0x12345678u);
}

delta::DpiArg PackedFormal(delta::DataTypeKind type, uint32_t width) {
  delta::DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = delta::Direction::kInput;
  formal.width = width;
  return formal;
}

TEST(DpiCanonicalUtilities, APartSelectIsASliceOfAPackedBitOrLogicArray) {
  using delta::DataTypeKind;
  EXPECT_TRUE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kBit, 8)));
  EXPECT_TRUE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kLogic, 18)));
  EXPECT_TRUE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kReg, 2)));
  EXPECT_TRUE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kInteger, 0)));
  EXPECT_TRUE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kTime, 0)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kBit, 1)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kLogic, 1)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kInt, 0)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kReal, 0)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kString, 0)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kChandle, 0)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kStruct, 0)));
}

TEST(DpiCanonicalUtilities, APartSelectReachesAtMostThirtyTwoBits) {
  EXPECT_EQ(delta::kDpiPartSelectMaxWidth, 32);
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(64, 0, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(64, 32, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(64, 0, 1));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(64, 0, 33));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(64, 0, 0));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(64, 0, -1));
}

TEST(DpiCanonicalUtilities,
     APartSelectOutsideTheNormalizedRangeIsUndetermined) {
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(40, 8, 32));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(40, 9, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(40, 39, 1));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(40, 40, 1));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(40, -1, 8));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(18, 0, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(18, 0, 18));
}

TEST(DpiCanonicalUtilities, TheUtilitiesIndexTheNormalizedRange) {
  const delta::SvActualDimension kAscending{4, 7};
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kAscending, 7), 0);
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kAscending, 6), 1);
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kAscending, 4), 3);
  const delta::SvActualDimension kDescending{17, 0};
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kDescending, 0), 0);
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kDescending, 17), 17);
  const delta::SvActualDimension kNegative{-1, -8};
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kNegative, -8), 0);
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kNegative, -1), 7);
  const svBitVecVal kA = 0x0Au;
  EXPECT_EQ(svGetBitselBit(&kA, delta::DpiNormalizedBitIndex(kAscending, 7)),
            0U);
  EXPECT_EQ(svGetBitselBit(&kA, delta::DpiNormalizedBitIndex(kAscending, 6)),
            1U);
  EXPECT_EQ(svGetBitselBit(&kA, delta::DpiNormalizedBitIndex(kAscending, 4)),
            1U);
}

}  // namespace
