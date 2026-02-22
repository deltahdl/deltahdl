// §19.5.1: Specifying bins for values

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulation/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.5.1-19.5.3: Explicit bins
// =============================================================================
TEST(Coverage, ExplicitBinCreation) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg");
  auto *cp = CoverageDB::AddCoverPoint(g, "addr");
  CoverBin bin;
  bin.name = "low";
  bin.kind = CoverBinKind::kExplicit;
  bin.values = {0, 1, 2, 3};
  auto *b = CoverageDB::AddBin(cp, bin);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->name, "low");
  EXPECT_EQ(b->values.size(), 4u);
}

// =============================================================================
// S19.5.1-19.5.3: Explicit bins
// =============================================================================
TEST(Coverage, SampleHitsExplicitBin) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg");
  auto *cp = CoverageDB::AddCoverPoint(g, "val");
  CoverBin bin;
  bin.name = "ones";
  bin.values = {1};
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"val", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);

  db.Sample(g, {{"val", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);  // No change.

  db.Sample(g, {{"val", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 2u);
}

// =============================================================================
// S19.5.1-19.5.3: Auto bins
// =============================================================================
TEST(Coverage, AutoBinCreation) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg");
  auto *cp = CoverageDB::AddCoverPoint(g, "addr");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 7);
  EXPECT_EQ(cp->bins.size(), 4u);

  // Each bin should cover 2 values: [0,1], [2,3], [4,5], [6,7].
  struct {
    size_t bin_idx;
    size_t val_idx;
    int64_t expected;
  } const kCases[] = {
      {0, 0, 0},
      {0, 1, 1},
      {3, 0, 6},
      {3, 1, 7},
  };
  for (const auto &c : kCases) {
    EXPECT_EQ(cp->bins[c.bin_idx].values[c.val_idx], c.expected);
  }
  EXPECT_EQ(cp->bins[0].values.size(), 2u);
}

TEST(Coverage, AutoBinSmallRange) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg");
  auto *cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 64;
  CoverageDB::AutoCreateBins(cp, 0, 3);
  // Range is 4, smaller than auto_bin_count=64, so only 4 bins.
  EXPECT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].values.size(), 1u);
  EXPECT_EQ(cp->bins[0].values[0], 0);
}

}  // namespace
