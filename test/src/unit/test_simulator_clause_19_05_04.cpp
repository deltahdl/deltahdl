#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, TransitionBinNotMatchedByScalar) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "sig");
  CoverBin tbin;
  tbin.name = "t_01";
  tbin.kind = CoverBinKind::kTransition;
  tbin.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, tbin);

  db.Sample(g, {{"sig", 0}});
  db.Sample(g, {{"sig", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

}
