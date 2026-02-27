// §19.6: Defining cross coverage

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulation/coverage.h"

#include "helpers_coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.6: Cross coverage
// =============================================================================
TEST(Coverage, CrossCoverageCreation) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);
  EXPECT_EQ(g->crosses.size(), 1u);
  EXPECT_EQ(g->crosses[0].bins.size(), 2u);
}

TEST(Coverage, CrossCoverageSampling) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);

  db.Sample(g, {{"a", 0}, {"b", 0}});
  EXPECT_EQ(g->crosses[0].bins[0].hit_count, 1u);
  EXPECT_EQ(g->crosses[0].bins[1].hit_count, 0u);

  db.Sample(g, {{"a", 1}, {"b", 1}});
  EXPECT_EQ(g->crosses[0].bins[1].hit_count, 1u);
}

}  // namespace
