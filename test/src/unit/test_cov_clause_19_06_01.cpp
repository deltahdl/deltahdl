// §19.6.1: Defining cross coverage bins

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>
#include "simulation/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.6.1: Cross bins coverage computation
// =============================================================================
TEST(Coverage, CrossCoverageComputation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "a");
  CoverageDB::AddCoverPoint(g, "b");

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};
  CrossBin cb;
  cb.name = "a0_b0";
  cb.value_sets = {{0}, {0}};
  cross.bins.push_back(cb);
  cb.name = "a1_b1";
  cb.value_sets = {{1}, {1}};
  cross.bins.push_back(cb);
  CoverageDB::AddCross(g, cross);

  db.Sample(g, {{"a", 0}, {"b", 0}});
  // 1 out of 2 cross bins covered.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&g->crosses[0]), 50.0);
}

}  // namespace
