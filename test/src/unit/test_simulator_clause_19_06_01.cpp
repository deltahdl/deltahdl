// §19.6.1: Defining cross coverage bins

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "helpers_coverage.h"
#include "simulator/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.6.1: Cross bins coverage computation
// =============================================================================
TEST(Coverage, CrossCoverageComputation) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);

  db.Sample(g, {{"a", 0}, {"b", 0}});
  // 1 out of 2 cross bins covered.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&g->crosses[0]), 50.0);
}

}  // namespace
