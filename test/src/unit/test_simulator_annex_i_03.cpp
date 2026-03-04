#include <gtest/gtest.h>

#include "simulator/svdpi.h"

namespace {

TEST(SvDpi, ScalarTypeSizes) {
  EXPECT_EQ(sizeof(svScalar), 1u);
  EXPECT_EQ(sizeof(svBit), 1u);
  EXPECT_EQ(sizeof(svLogic), 1u);
}

TEST(SvDpi, MaskMacro) {
  EXPECT_EQ(SV_MASK(1), 1u);
  EXPECT_EQ(SV_MASK(4), 0xFu);
  EXPECT_EQ(SV_MASK(8), 0xFFu);
}

TEST(SvDpi, PartSelectBit) {
  svBitVecVal src = 0xABCD;
  svBitVecVal dst = 0;
  svGetPartselBit(&dst, &src, 4, 8);
  EXPECT_EQ(dst, 0xBCu);
}

TEST(SvDpi, CanonicalValueConstants) {
  EXPECT_EQ(sv_0, 0);
  EXPECT_EQ(sv_1, 1);
  EXPECT_EQ(sv_z, 2);
  EXPECT_EQ(sv_x, 3);
}

}
