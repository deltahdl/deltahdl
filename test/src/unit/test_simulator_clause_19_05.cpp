// §19.5: Defining coverage points

#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulation/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.5: Coverpoint declaration
// =============================================================================
TEST(Coverage, AddCoverPointToGroup) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg");
  auto *cp = CoverageDB::AddCoverPoint(g, "addr");
  ASSERT_NE(cp, nullptr);
  EXPECT_EQ(cp->name, "addr");
  EXPECT_EQ(g->coverpoints.size(), 1u);
}

// =============================================================================
// S19.5: Coverpoint with iff guard
// =============================================================================
TEST(Coverage, IffGuardBlocksSampling) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg");
  auto *cp = CoverageDB::AddCoverPoint(g, "x");
  cp->has_iff_guard = true;
  cp->iff_guard_value = false;  // Guard is disabled.

  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);  // Blocked by iff.
}

TEST(Coverage, IffGuardAllowsSampling) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg");
  auto *cp = CoverageDB::AddCoverPoint(g, "x");
  cp->has_iff_guard = true;
  cp->iff_guard_value = true;  // Guard is enabled.

  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

}  // namespace
