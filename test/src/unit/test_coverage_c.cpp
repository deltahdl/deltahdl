// Non-LRM tests

#include <gtest/gtest.h>
#include <string>
#include <vector>
#include "simulation/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.5.5: Wildcard bins
// =============================================================================
TEST(Coverage, WildcardBinMatchesValues) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "data");
  CoverBin wbin;
  wbin.name = "w_even";
  wbin.kind = CoverBinKind::kWildcard;
  wbin.values = {0, 2, 4, 6};  // Even values.
  CoverageDB::AddBin(cp, wbin);

  db.Sample(g, {{"data", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);

  db.Sample(g, {{"data", 3}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);  // Odd, no match.
}

// =============================================================================
// S19.5.6: Illegal bins
// =============================================================================
TEST(Coverage, IllegalBinsNotSampled) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  CoverBin ib;
  ib.name = "bad_addr";
  ib.kind = CoverBinKind::kIllegal;
  ib.values = {0xFF};
  CoverageDB::AddBin(cp, ib);

  db.Sample(g, {{"addr", 0xFF}});
  // Illegal bins should not be hit during sampling.
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, IllegalBinsExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin good;
  good.name = "valid";
  good.values = {1};
  CoverageDB::AddBin(cp, good);

  CoverBin bad;
  bad.name = "illegal";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {0xFF};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"x", 1}});
  // Only the valid bin counts: 1 covered out of 1.
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

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
