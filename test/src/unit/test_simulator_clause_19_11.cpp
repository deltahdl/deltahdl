// §19.11: Coverage computation

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulation/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, AutoBinSampleAndCoverage) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg");
  auto *cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 3);

  // Hit all bins.
  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  db.Sample(g, {{"x", 2}});
  db.Sample(g, {{"x", 3}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

// =============================================================================
// Edge case: empty covergroup coverage
// =============================================================================
TEST(Coverage, EmptyGroupCoverageIsZero) {
  CoverageDB db;
  auto *g = db.CreateGroup("empty");
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 0.0);
}

TEST(Coverage, PointCoverageWithNoBinsIs100) {
  CoverPoint cp;
  cp.name = "empty_cp";
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(&cp), 100.0);
}

// =============================================================================
// Multiple coverpoints in one group
// =============================================================================
TEST(Coverage, MultipleCoverpointsAveraged) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg");

  auto *cp1 = CoverageDB::AddCoverPoint(g, "a");
  CoverBin b1;
  b1.name = "b0";
  b1.values = {0};
  CoverageDB::AddBin(cp1, b1);

  auto *cp2 = CoverageDB::AddCoverPoint(g, "b");
  CoverBin b2;
  b2.name = "b0";
  b2.values = {0};
  CoverageDB::AddBin(cp2, b2);

  // Only cover "a", not "b".
  db.Sample(g, {{"a", 0}, {"b", 99}});
  // a=100%, b=0% => average = 50%.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 50.0);
}

}  // namespace
