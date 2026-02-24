// Annex H.7.7: Canonical representation of packed arrays

#include <gtest/gtest.h>
#include "vpi/svdpi.h"

namespace {

TEST(SvDpi, PackedArrayTypeSizes) {
  EXPECT_EQ(sizeof(svBitVecVal), 4u);
  EXPECT_EQ(sizeof(svLogicVecVal), 8u);
}

}  // namespace
