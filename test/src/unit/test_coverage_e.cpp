// Non-LRM tests

#include <gtest/gtest.h>
#include <string>
#include <vector>
#include "simulation/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.7: Coverage options: at_least, weight, goal
// =============================================================================
TEST(Coverage, GoalOption) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.goal = 90.0;
  EXPECT_DOUBLE_EQ(g->options.goal, 90.0);
}

// =============================================================================
// S19.8: Coverage methods
// =============================================================================
TEST(Coverage, SampleCountIncremented) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "x");

  EXPECT_EQ(g->sample_count, 0u);
  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->sample_count, 1u);
  db.Sample(g, {{"x", 1}});
  EXPECT_EQ(g->sample_count, 2u);
}

TEST(Coverage, GetCoveragePercentage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b1;
  b1.name = "b0";
  b1.values = {0};
  CoverageDB::AddBin(cp, b1);

  CoverBin b2;
  b2.name = "b1";
  b2.values = {1};
  CoverageDB::AddBin(cp, b2);

  db.Sample(g, {{"x", 0}});
  // 1 of 2 bins covered.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 50.0);
}

TEST(Coverage, GetInstCoverageMatchesGetCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetInstCoverage(g), CoverageDB::GetCoverage(g));
}

// =============================================================================
// S19.9: $get_coverage system function
// =============================================================================
TEST(Coverage, GlobalCoverageEmpty) {
  CoverageDB db;
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 0.0);
}

}  // namespace
