#include <gtest/gtest.h>

#include "simulator/svdpi.h"

namespace {

TEST(SvDpi, LogicVecValLayout) {
  svLogicVecVal val;
  val.aval = 0xDEADBEEF;
  val.bval = 0xCAFEBABE;
  EXPECT_EQ(val.aval, 0xDEADBEEFu);
  EXPECT_EQ(val.bval, 0xCAFEBABEu);
}

TEST(SvDpi, PackedDataNelems) {
  // Degenerate zero-width packed array needs no 32-bit chunks at all.
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(0), 0);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(1), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(32), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(33), 2);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(65), 3);
  // Wider widths keep rounding up at each 32-bit chunk boundary.
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(96), 3);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(97), 4);
}

TEST(SvDpi, GetUnsignedBits) {
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFF, 4), 0xFu);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFFFFFFF, 32), 0xFFFFFFFFu);
  // Every bit above the requested width is dropped, even when all set.
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFFFFFFF, 4), 0xFu);
  // Narrowest non-trivial width keeps only bit 0.
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0x3, 1), 0x1u);
}

TEST(SvDpi, MaskCoversLowBits) {
  // SV_MASK(N) yields the low N bits set so callers can discard the
  // undetermined contents of unused high bits.
  EXPECT_EQ(SV_MASK(4), 0xFu);
  EXPECT_EQ(SV_MASK(8), 0xFFu);
  EXPECT_EQ(SV_MASK(16), 0xFFFFu);
  // Boundary widths: a single low bit and one short of the full word.
  EXPECT_EQ(SV_MASK(1), 0x1u);
  EXPECT_EQ(SV_MASK(31), 0x7FFFFFFFu);
}

TEST(SvDpi, GetSignedBits) {
  // Bit N decides extension: set -> sign-extend into the high bits,
  // clear -> mask to the low N bits; width 32 passes the value through.
  // Feed the inputs through runtime values so the macro does not collapse
  // into compile-time-constant bitwise sub-expressions.
  uint32_t sign_set_4 = 0x1F;
  uint32_t sign_clear_4 = 0x0F;
  uint32_t passthrough_32 = 0x12345678;
  EXPECT_EQ(static_cast<uint32_t>(SV_GET_SIGNED_BITS(sign_set_4, 4)),
            0xFFFFFFFFu);
  EXPECT_EQ(static_cast<uint32_t>(SV_GET_SIGNED_BITS(sign_clear_4, 4)),
            0x0000000Fu);
  EXPECT_EQ(static_cast<uint32_t>(SV_GET_SIGNED_BITS(passthrough_32, 32)),
            0x12345678u);
  // High junk above the width is discarded regardless of the sign bit:
  // bit N clear -> masked to low bits; bit N set -> still sign-extended.
  EXPECT_EQ(static_cast<uint32_t>(SV_GET_SIGNED_BITS(0xFF0F, 4)), 0x0000000Fu);
  EXPECT_EQ(static_cast<uint32_t>(SV_GET_SIGNED_BITS(0xFF1F, 4)), 0xFFFFFFFFu);
}

TEST(SvDpi, VpiVecvalSharedStruct) {
  s_vpi_vecval vec;
  vec.aval = 1;
  vec.bval = 0;
  EXPECT_EQ(vec.aval, 1u);
  EXPECT_EQ(vec.bval, 0u);
}

TEST(SvDpi, PackedArrayTypeSizes) {
  EXPECT_EQ(sizeof(svBitVecVal), 4u);
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
}

}  // namespace
