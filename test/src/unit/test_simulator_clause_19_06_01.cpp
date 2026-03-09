#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "helpers_coverage.h"
#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, CrossCoverageComputation) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);

  db.Sample(g, {{"a", 0}, {"b", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&g->crosses[0]), 50.0);
}

}  // namespace
