// §19.5.1: Specifying bins for values

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>
#include "simulation/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.5.1-19.5.3: Explicit bins
// =============================================================================
TEST(Coverage, ExplicitBinCreation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  CoverBin bin;
  bin.name = "low";
  bin.kind = CoverBinKind::kExplicit;
  bin.values = {0, 1, 2, 3};
  auto* b = CoverageDB::AddBin(cp, bin);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->name, "low");
  EXPECT_EQ(b->values.size(), 4u);
}

// =============================================================================
// S19.5.1-19.5.3: Explicit bins
// =============================================================================
TEST(Coverage, SampleHitsExplicitBin) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "val");
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

}  // namespace
