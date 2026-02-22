// §19.5.7: Value resolution

#include <gtest/gtest.h>
#include <string>
#include <vector>
#include "simulation/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.5.7: Ignore bins
// =============================================================================
TEST(Coverage, IgnoreBinsNotSampled) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "data");
  CoverBin ign;
  ign.name = "skip_zero";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {0};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"data", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, IgnoreBinsExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin good;
  good.name = "valid";
  good.values = {1};
  CoverageDB::AddBin(cp, good);

  CoverBin ign;
  ign.name = "ignored";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {0};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"x", 1}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

}  // namespace
