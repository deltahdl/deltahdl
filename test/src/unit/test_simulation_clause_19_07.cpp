// §19.7: Specifying coverage options

#include <gtest/gtest.h>
#include <string>
#include <vector>
#include "simulation/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.7: Coverage options: at_least, weight, goal
// =============================================================================
TEST(Coverage, AtLeastOption) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin bin;
  bin.name = "b0";
  bin.values = {0};
  bin.at_least = 3;
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 0}});
  // 2 hits, at_least=3 => not covered yet.
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 0.0);

  db.Sample(g, {{"x", 0}});
  // 3 hits, at_least=3 => covered.
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(Coverage, WeightOption) {
  CoverageDB db;
  auto* g1 = db.CreateGroup("cg1");
  g1->options.weight = 2;
  auto* cp1 = CoverageDB::AddCoverPoint(g1, "x");
  CoverBin b1;
  b1.name = "b";
  b1.values = {0};
  CoverageDB::AddBin(cp1, b1);
  db.Sample(g1, {{"x", 0}});  // 100% coverage, weight=2.

  auto* g2 = db.CreateGroup("cg2");
  g2->options.weight = 1;
  auto* cp2 = CoverageDB::AddCoverPoint(g2, "y");
  CoverBin b2;
  b2.name = "b";
  b2.values = {0};
  CoverageDB::AddBin(cp2, b2);
  // 0% coverage, weight=1.

  // Global: (100*2 + 0*1) / (2+1) = 200/3 ~ 66.67.
  double global = db.GetGlobalCoverage();
  EXPECT_NEAR(global, 200.0 / 3.0, 0.01);
}

}  // namespace
