#include <gtest/gtest.h>

#include <type_traits>

#include "simulator/svdpi.h"

namespace {

// H.10.1.1 fixes the canonical codes for scalar values crossing the DPI:
// 0 and 1 for the two-state values, z and x for the extra four-state values.
TEST(SvDpi, ScalarCanonicalCodes) {
  EXPECT_EQ(sv_0, 0);
  EXPECT_EQ(sv_1, 1);
  EXPECT_EQ(sv_z, 2);
  EXPECT_EQ(sv_x, 3);
}

// svScalar is the single byte-wide carrier the header uses for every scalar
// value, so each of the four canonical codes fits without truncation.
TEST(SvDpi, ScalarTypeIsSingleByte) {
  EXPECT_EQ(sizeof(svScalar), 1u);
  EXPECT_TRUE(std::is_unsigned<svScalar>::value);
  svScalar codes[] = {sv_0, sv_1, sv_z, sv_x};
  EXPECT_EQ(codes[0], 0);
  EXPECT_EQ(codes[3], 3);
}

// Both bit and logic scalars are spelled as the common svScalar type, so the
// three names denote one and the same underlying representation.
TEST(SvDpi, BitAndLogicShareScalarType) {
  EXPECT_TRUE((std::is_same<svBit, svScalar>::value));
  EXPECT_TRUE((std::is_same<svLogic, svScalar>::value));
  EXPECT_TRUE((std::is_same<svBit, svLogic>::value));
}

// Edge case: the four scalar codes must map to four different values, otherwise
// two of the logic states would be indistinguishable once encoded.
TEST(SvDpi, ScalarCodesAreDistinct) {
  const int codes[] = {sv_0, sv_1, sv_z, sv_x};
  for (int i = 0; i < 4; ++i) {
    for (int j = i + 1; j < 4; ++j) {
      EXPECT_NE(codes[i], codes[j]) << "codes " << i << " and " << j;
    }
  }
  // The codes occupy exactly the low two bits, so none exceeds the value 3.
  for (int code : codes) {
    EXPECT_GE(code, 0);
    EXPECT_LE(code, 3);
  }
}

// Edge case: every canonical code survives a round trip through svScalar with no
// truncation, since the carrier is the type used to pass scalars across the DPI.
TEST(SvDpi, AllScalarCodesRoundTripThroughCarrier) {
  const int codes[] = {sv_0, sv_1, sv_z, sv_x};
  for (int code : codes) {
    svScalar stored = static_cast<svScalar>(code);
    EXPECT_EQ(static_cast<int>(stored), code);
  }
}

}
