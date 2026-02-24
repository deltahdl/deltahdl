// Annex H.10.1.2: Canonical representation of packed arrays

#include <gtest/gtest.h>
#include "vpi/svdpi.h"

namespace {

TEST(SvDpi, LogicVecValLayout) {
  svLogicVecVal val;
  val.aval = 0xDEADBEEF;
  val.bval = 0xCAFEBABE;
  EXPECT_EQ(val.aval, 0xDEADBEEFu);
  EXPECT_EQ(val.bval, 0xCAFEBABEu);
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

TEST(SvDpi, PackedArrayTypeSizes) {
  EXPECT_EQ(sizeof(svBitVecVal), 4u);
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
}

TEST(DpiRuntime, SvLogicVecValLayout) {
  SvLogicVecVal v;
  v.aval = 0xDEADBEEF;
  v.bval = 0;
  EXPECT_EQ(v.aval, 0xDEADBEEFu);
  EXPECT_TRUE(v.bval == 0);  // Known value.
}

}  // namespace
