// §19.9: Predefined coverage system tasks and system functions

#include "simulation/coverage.h"
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace delta;

namespace {

// =============================================================================
// S19.9: $get_coverage system function
// =============================================================================
TEST(Coverage, GlobalCoverageEmpty) {
  CoverageDB db;
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 0.0);
}

} // namespace
