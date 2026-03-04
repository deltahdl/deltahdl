// Annex H.7.7: Canonical representation of packed arrays

#include <gtest/gtest.h>

#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

// =============================================================================
// svdpi.h type mapping (S35.5)
// =============================================================================
TEST(DpiRuntime, SvBitVecValSize) { EXPECT_EQ(sizeof(SvBitVecVal), 4u); }

}  // namespace
