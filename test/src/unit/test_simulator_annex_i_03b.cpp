// Annex I.3: Source code

#include "simulation/dpi_runtime.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace delta;

namespace {

// =============================================================================
// svdpi.h type mapping (S35.5)
// =============================================================================
TEST(DpiRuntime, SvBitVecValSize) { EXPECT_EQ(sizeof(SvBitVecVal), 4u); }

TEST(DpiRuntime, SvLogicVecValLayout) {
  SvLogicVecVal v;
  v.aval = 0xDEADBEEF;
  v.bval = 0;
  EXPECT_EQ(v.aval, 0xDEADBEEFu);
  EXPECT_TRUE(v.bval == 0); // Known value.
}

} // namespace
