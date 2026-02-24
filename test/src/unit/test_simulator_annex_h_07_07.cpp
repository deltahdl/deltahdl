// Annex H.7.7: Canonical representation of packed arrays

#include <gtest/gtest.h>
#include "vpi/svdpi.h"

namespace {

TEST(SvDpi, PackedArrayTypeSizes) {
  EXPECT_EQ(sizeof(svBitVecVal), 4u);
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
}

// =============================================================================
// svdpi.h type mapping (S35.5)
// =============================================================================
TEST(DpiRuntime, SvBitVecValSize) { EXPECT_EQ(sizeof(SvBitVecVal), 4u); }

TEST(DpiRuntime, SvLogicVecValLayout) {
  SvLogicVecVal v;
  v.aval = 0xDEADBEEF;
  v.bval = 0;
  EXPECT_EQ(v.aval, 0xDEADBEEFu);
  EXPECT_TRUE(v.bval == 0);  // Known value.
}

}  // namespace
