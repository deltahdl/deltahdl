#include <gtest/gtest.h>

#include <cstdint>

#include "parser/ast.h"
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

// Annex H.11.5: a put part-select writes source bits [w-1:0] into destination
// bits [(i+w-1):i] without disturbing the surrounding destination bits.
TEST(SvDpi, PutPartSelectBitPreservesSurrounding) {
  svBitVecVal dst = 0xFFFFFFFFu;
  svBitVecVal src = 0x00u;  // clear the slice [11:4]
  svPutPartselBit(&dst, src, 4, 8);
  EXPECT_EQ((dst >> 4) & 0xFFu, 0u);  // slice written
  EXPECT_EQ(dst & 0xFu, 0xFu);        // bits [3:0] untouched
  EXPECT_EQ(dst >> 12, 0xFFFFFu);     // bits [31:12] untouched
}

TEST(SvDpi, PutPartSelectLogicPreservesSurrounding) {
  svLogicVecVal dst;
  dst.aval = 0xFFFFFFFFu;
  dst.bval = 0x00000000u;
  svLogicVecVal src;
  src.aval = 0x00u;  // clear the aval slice [11:4]
  src.bval = 0x00u;
  svPutPartselLogic(&dst, src, 4, 8);
  EXPECT_EQ((dst.aval >> 4) & 0xFFu, 0u);  // slice written
  EXPECT_EQ(dst.aval & 0xFu, 0xFu);        // bits [3:0] untouched
  EXPECT_EQ(dst.aval >> 12, 0xFFFFFu);     // bits [31:12] untouched
  EXPECT_EQ(dst.bval, 0u);                 // bval untouched
}

// Annex H.11.5: a get part-select reads source bits [(i+w-1):i] into
// destination bits [w-1:0], and for w < 32 leaves destination bits [31:w]
// unchanged.
TEST(SvDpi, GetPartSelectBitPreservesHighBits) {
  svBitVecVal src = 0xABCDEF12u;
  svBitVecVal dst = 0xFFFFFFFFu;
  svGetPartselBit(&dst, &src, 4, 8);
  // Low w bits hold the slice [11:4] of the source.
  EXPECT_EQ(dst & 0xFFu, (src >> 4) & 0xFFu);
  // Surrounding destination bits [31:8] are left unchanged.
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

// Annex H.11.5 edge case: bit-selects index the canonical word array by
// i/32, so selects beyond bit 31 must reach the correct word.
TEST(SvDpi, BitSelectUpperWord) {
  svBitVecVal bv[3] = {0u, 0u, 0u};
  bv[2] = 1u << 2;  // bit index 66 set
  EXPECT_EQ(svGetBitselBit(bv, 66), 1u);
  EXPECT_EQ(svGetBitselBit(bv, 65), 0u);

  svPutBitselBit(bv, 33, 1);
  EXPECT_EQ(bv[1], 1u << 1);  // bit index 33 lands in word 1
  svPutBitselBit(bv, 66, 0);
  EXPECT_EQ(bv[2], 0u);
}

TEST(SvDpi, BitSelectLogicUpperWord) {
  svLogicVecVal lv[3] = {{0, 0}, {0, 0}, {0, 0}};
  svPutBitselLogic(lv, 34, sv_z);  // word 1, bit 2
  EXPECT_EQ(lv[1].aval, 0u);
  EXPECT_EQ(lv[1].bval, 1u << 2);
  EXPECT_EQ(svGetBitselLogic(lv, 34), sv_z);
}

// Annex H.11.5 edge case: a get part-select whose range [(i+w-1):i] crosses a
// 32-bit canonical word boundary assembles the slice from both words while
// still preserving destination bits [31:w].
TEST(SvDpi, GetPartSelectBitAcrossWordBoundary) {
  svBitVecVal src[2] = {0x80000000u, 0x0000000Fu};
  svBitVecVal dst = 0xFFFFFFFFu;
  svGetPartselBit(&dst, src, 28, 8);
  // bits [31:28] of word 0 give 0x8, bits [35:32] of word 1 give 0xF.
  EXPECT_EQ(dst & 0xFFu, 0xF8u);
  EXPECT_EQ(dst >> 8, 0xFFFFFFu);  // surrounding bits preserved
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

// Annex H.11.5 edge case: a put part-select whose destination range crosses a
// word boundary updates both words and leaves the surrounding bits unchanged.
TEST(SvDpi, PutPartSelectBitAcrossWordBoundary) {
  svBitVecVal dst[2] = {0x0FFFFFFFu, 0xFFFFFFF0u};
  svPutPartselBit(dst, 0xFFu, 28, 8);
  EXPECT_EQ(dst[0], 0xFFFFFFFFu);  // top nibble of word 0 set
  EXPECT_EQ(dst[1], 0xFFFFFFFFu);  // low nibble of word 1 set
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

// Annex H.11.5 edge case: w == 32 is the maximum part-select width; the whole
// destination word is written (the "preserve [31:w]" carve-out applies only to
// w < 32).
TEST(SvDpi, PartSelectFullWidthWord) {
  svBitVecVal src = 0xDEADBEEFu;
  svBitVecVal getdst = 0x12345678u;
  svGetPartselBit(&getdst, &src, 0, 32);
  EXPECT_EQ(getdst, 0xDEADBEEFu);

  svBitVecVal putdst = 0u;
  svPutPartselBit(&putdst, 0xDEADBEEFu, 0, 32);
  EXPECT_EQ(putdst, 0xDEADBEEFu);
}

// Annex H.11.5 error condition: part-selects are limited to at most 32 bits.
// Widths outside (0, 32] are not applied, leaving the destination untouched.
TEST(SvDpi, PartSelectWidthOutOfRangeIsNoOp) {
  svBitVecVal src = 0xFFFFFFFFu;
  svBitVecVal getdst = 0x12345678u;
  svGetPartselBit(&getdst, &src, 0, 33);  // too wide
  EXPECT_EQ(getdst, 0x12345678u);
  svGetPartselBit(&getdst, &src, 0, 0);  // zero width
  EXPECT_EQ(getdst, 0x12345678u);

  svBitVecVal putdst = 0x12345678u;
  svPutPartselBit(&putdst, 0xFFu, 0, 33);
  EXPECT_EQ(putdst, 0x12345678u);
  svPutPartselBit(&putdst, 0xFFu, 0, 0);
  EXPECT_EQ(putdst, 0x12345678u);
}

// Annex H.11.5 as a statement about the C layer: what the bit-select and
// part-select utilities apply to, the limit on a part-select's width, when a
// part-select's behavior is determined at all, and the normalized index of
// §H.7.6 both utilities take.

delta::DpiArg PackedFormal(delta::DataTypeKind type, uint32_t width) {
  delta::DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = delta::Direction::kInput;
  formal.width = width;
  return formal;
}

// §H.11.5: a part-select is a slice of a packed array of type bit or logic
// -- reg being logic, integer and time packed 4-state -- and there is no
// slice of an unpacked array, a scalar, or a type with no canonical form.
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
  // A scalar bit or logic is a small type passed by value (§H.8.7), not a
  // packed array in canonical form.
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

// §H.11.5: the part-select functions reach a narrow subrange of up to 32
// bits; 32 is the limit itself and 33 is beyond it, and a width of no bits
// selects nothing.
TEST(DpiCanonicalUtilities, APartSelectReachesAtMostThirtyTwoBits) {
  EXPECT_EQ(delta::kDpiPartSelectMaxWidth, 32);
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(64, 0, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(64, 32, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(64, 0, 1));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(64, 0, 33));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(64, 0, 0));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(64, 0, -1));
}

// §H.11.5: where the range [(i+w-1):i] a part-select names is not fully
// within the array's normalized range [n-1:0] the behavior is undetermined
// -- so of a 40-bit array bits [39:8] are determined and bits [40:9], one
// past the MSB, are not, nor is a range starting below bit 0.
TEST(DpiCanonicalUtilities,
     APartSelectOutsideTheNormalizedRangeIsUndetermined) {
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(40, 8, 32));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(40, 9, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(40, 39, 1));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(40, 40, 1));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(40, -1, 8));
  // A width the limit allows is still undetermined on an array narrower
  // than it.
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(18, 0, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(18, 0, 18));
}

// §H.11.5 with §H.7.6 b): the utilities index the normalized range [n-1:0],
// 0 the LSB, whatever range the declaration ran over -- so in `bit [4:7] a`
// the bit a[7] is at index 0 and a[4] at index 3, in `logic [17:0] b` b[k]
// is at index k, and in `bit [-1:-8] c` c[-8] is at 0 and c[-1] at 7.
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
  // The index so found is what the bit-select utility takes: with a holding
  // 4'b1010 in canonical form, a[7], the LSB, is 0 and a[6] is 1.
  const svBitVecVal kA = 0x0Au;
  EXPECT_EQ(svGetBitselBit(&kA, delta::DpiNormalizedBitIndex(kAscending, 7)),
            0U);
  EXPECT_EQ(svGetBitselBit(&kA, delta::DpiNormalizedBitIndex(kAscending, 6)),
            1U);
  EXPECT_EQ(svGetBitselBit(&kA, delta::DpiNormalizedBitIndex(kAscending, 4)),
            1U);
}

}  // namespace
