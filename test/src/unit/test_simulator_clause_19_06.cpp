// §19.6: Defining cross coverage

#include <gtest/gtest.h>
#include <string>
#include <vector>
#include "simulation/coverage.h"

using namespace delta;

namespace {

// =============================================================================
// S19.6: Cross coverage
// =============================================================================
TEST(Coverage, CrossCoverageCreation) {
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
  EXPECT_EQ(g->crosses.size(), 1u);
  EXPECT_EQ(g->crosses[0].bins.size(), 2u);
}

TEST(Coverage, CrossCoverageSampling) {
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
  EXPECT_EQ(g->crosses[0].bins[0].hit_count, 1u);
  EXPECT_EQ(g->crosses[0].bins[1].hit_count, 0u);

  db.Sample(g, {{"a", 1}, {"b", 1}});
  EXPECT_EQ(g->crosses[0].bins[1].hit_count, 1u);
}

}  // namespace
