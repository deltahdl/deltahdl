// §19.5.5: Excluding coverage point values or transitions

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
  auto *g = db.CreateGroup("cg");
  auto *cp = CoverageDB::AddCoverPoint(g, "data");
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

}  // namespace
