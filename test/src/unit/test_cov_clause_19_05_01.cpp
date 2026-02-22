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

}  // namespace
