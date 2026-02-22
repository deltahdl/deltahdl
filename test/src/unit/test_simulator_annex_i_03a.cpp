// Annex I.3: svdpi.h source code

#include <gtest/gtest.h>

#include "vpi/svdpi.h"

namespace {

// =============================================================================
// Canonical 4-value constants (Annex I)
// =============================================================================

TEST(SvDpi, CanonicalValueConstants) {
  EXPECT_EQ(sv_0, 0);
  EXPECT_EQ(sv_1, 1);
  EXPECT_EQ(sv_z, 2);
  EXPECT_EQ(sv_x, 3);
}

// =============================================================================
// Type sizes and layout (Annex I)
// =============================================================================

TEST(SvDpi, ScalarTypeSizes) {
  EXPECT_EQ(sizeof(svScalar), 1u);
  EXPECT_EQ(sizeof(svBit), 1u);
  EXPECT_EQ(sizeof(svLogic), 1u);
}

TEST(SvDpi, PackedArrayTypeSizes) {
  EXPECT_EQ(sizeof(svBitVecVal), 4u);
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
}

TEST(SvDpi, LogicVecValLayout) {
  svLogicVecVal val;
  val.aval = 0xDEADBEEF;
  val.bval = 0xCAFEBABE;
  EXPECT_EQ(val.aval, 0xDEADBEEFu);
  EXPECT_EQ(val.bval, 0xCAFEBABEu);
}

TEST(SvDpi, HandleTypes) {
  svScope scope = nullptr;
  svOpenArrayHandle arr = nullptr;
  EXPECT_EQ(scope, nullptr);
  EXPECT_EQ(arr, nullptr);
}

// =============================================================================
// Packed array utility macros (Annex I)
// =============================================================================

TEST(SvDpi, PackedDataNelems) {
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(1), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(32), 1);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(33), 2);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(64), 2);
  EXPECT_EQ(SV_PACKED_DATA_NELEMS(65), 3);
}

TEST(SvDpi, MaskMacro) {
  EXPECT_EQ(SV_MASK(1), 1u);
  EXPECT_EQ(SV_MASK(4), 0xFu);
  EXPECT_EQ(SV_MASK(8), 0xFFu);
}

TEST(SvDpi, GetUnsignedBits) {
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFF, 4), 0xFu);
  EXPECT_EQ(SV_GET_UNSIGNED_BITS(0xFFFFFFFF, 32), 0xFFFFFFFFu);
}

// =============================================================================
// VPI shared structures (guarded by #ifndef)
// =============================================================================

TEST(SvDpi, VpiVecvalSharedStruct) {
  s_vpi_vecval vec;
  vec.aval = 1;
  vec.bval = 0;
  EXPECT_EQ(vec.aval, 1u);
  EXPECT_EQ(vec.bval, 0u);
}

TEST(SvDpi, TimeValAlias) {
  svTimeVal tv;
  tv.type = sv_sim_time;
  tv.high = 0;
  tv.low = 100;
  tv.real = 0.0;
  EXPECT_EQ(tv.type, vpiSimTime);
}

TEST(SvDpi, TimeConstants) {
  EXPECT_EQ(sv_scaled_real_time, vpiScaledRealTime);
  EXPECT_EQ(sv_sim_time, vpiSimTime);
}

// =============================================================================
// Bit-select utility functions (Annex I)
// =============================================================================

TEST(SvDpi, BitSelectBit) {
  svBitVecVal bv = 0x0A;  // binary: 1010
  EXPECT_EQ(svGetBitselBit(&bv, 0), 0u);
  EXPECT_EQ(svGetBitselBit(&bv, 1), 1u);
  EXPECT_EQ(svGetBitselBit(&bv, 2), 0u);
  EXPECT_EQ(svGetBitselBit(&bv, 3), 1u);
}

TEST(SvDpi, BitSelectLogic) {
  svLogicVecVal lv;
  lv.aval = 0x03;  // bits 0,1 = 1
  lv.bval = 0x02;  // bit 1 has bval set -> x
  // bit 0: aval=1, bval=0 -> sv_1
  EXPECT_EQ(svGetBitselLogic(&lv, 0), sv_1);
  // bit 1: aval=1, bval=1 -> sv_x
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
  svPutBitselLogic(&lv, 2, sv_z);  // z: aval=0, bval=1
  EXPECT_EQ(lv.aval & (1u << 2), 0u);
  EXPECT_EQ(lv.bval & (1u << 2), 4u);
}

// =============================================================================
// DPI scope functions (Annex I)
// =============================================================================

TEST(SvDpi, ScopeGetSetRoundTrip) {
  svScope old_scope = svGetScope();
  int dummy = 42;
  auto new_scope = reinterpret_cast<svScope>(&dummy);
  svScope prev = svSetScope(new_scope);
  EXPECT_EQ(prev, old_scope);
  EXPECT_EQ(svGetScope(), new_scope);
  svSetScope(old_scope);
}

TEST(SvDpi, DpiVersionReturnsNonNull) {
  const char *ver = svDpiVersion();
  ASSERT_NE(ver, nullptr);
  EXPECT_GT(strlen(ver), 0u);
}

// =============================================================================
// Part-select utility functions (Annex I)
// =============================================================================

TEST(SvDpi, PartSelectBit) {
  svBitVecVal src = 0xABCD;
  svBitVecVal dst = 0;
  svGetPartselBit(&dst, &src, 4, 8);  // extract bits [11:4] = 0xBC
  EXPECT_EQ(dst, 0xBCu);
}

TEST(SvDpi, PutPartSelectBit) {
  svBitVecVal dst = 0;
  svBitVecVal src = 0x0F;
  svPutPartselBit(&dst, src, 4, 8);  // insert 0x0F at bits [11:4]
  EXPECT_EQ(dst, 0xF0u);
}

}  // namespace
