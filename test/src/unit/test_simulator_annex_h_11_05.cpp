#include <gtest/gtest.h>

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

}
