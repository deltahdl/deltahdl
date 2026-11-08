#include <gtest/gtest.h>

#include <type_traits>

#include "simulator/svdpi.h"

namespace {

TEST(SvDpi, ScalarCanonicalCodes) {
  EXPECT_EQ(sv_0, 0);
  EXPECT_EQ(sv_1, 1);
  EXPECT_EQ(sv_z, 2);
  EXPECT_EQ(sv_x, 3);
}

TEST(SvDpi, ScalarTypeIsSingleByte) {
  EXPECT_EQ(sizeof(svScalar), 1u);
  EXPECT_TRUE(std::is_unsigned<svScalar>::value);
  svScalar codes[] = {sv_0, sv_1, sv_z, sv_x};
  EXPECT_EQ(codes[0], 0);
  EXPECT_EQ(codes[3], 3);
}

TEST(SvDpi, ScalarIsTheStandardsUnsignedChar) {
  EXPECT_TRUE((std::is_same<svScalar, unsigned char>::value));
}

TEST(SvDpi, BitAndLogicShareScalarType) {
  EXPECT_TRUE((std::is_same<svBit, svScalar>::value));
  EXPECT_TRUE((std::is_same<svLogic, svScalar>::value));
  EXPECT_TRUE((std::is_same<svBit, svLogic>::value));
}

TEST(SvDpi, ScalarCodesAreDistinct) {
  const int kCodes[] = {sv_0, sv_1, sv_z, sv_x};
  for (int i = 0; i < 4; ++i) {
    for (int j = i + 1; j < 4; ++j) {
      EXPECT_NE(kCodes[i], kCodes[j]) << "codes " << i << " and " << j;
    }
  }
  for (int code : kCodes) {
    EXPECT_GE(code, 0);
    EXPECT_LE(code, 3);
  }
}

TEST(SvDpi, AllScalarCodesRoundTripThroughCarrier) {
  const int kCodes[] = {sv_0, sv_1, sv_z, sv_x};
  for (int code : kCodes) {
    auto stored = static_cast<svScalar>(code);
    EXPECT_EQ(static_cast<int>(stored), code);
  }
}

}  // namespace
