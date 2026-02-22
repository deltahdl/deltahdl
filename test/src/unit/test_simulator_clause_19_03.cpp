// §19.3: Defining the coverage model: covergroup

#include "simulation/coverage.h"
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace delta;

namespace {

// =============================================================================
// S19.2-19.3: Covergroup definition and instantiation
// =============================================================================
TEST(Coverage, CreateGroupAndFind) {
  CoverageDB db;
  auto *g = db.CreateGroup("cg_addr");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->name, "cg_addr");
  EXPECT_EQ(db.GroupCount(), 1u);
  auto *found = db.FindGroup("cg_addr");
  EXPECT_EQ(found, g);
}

TEST(Coverage, FindNonexistentGroupReturnsNull) {
  CoverageDB db;
  EXPECT_EQ(db.FindGroup("missing"), nullptr);
}

TEST(Coverage, MultipleGroupInstances) {
  CoverageDB db;
  auto *g1 = db.CreateGroup("cg1");
  auto *g2 = db.CreateGroup("cg2");
  EXPECT_EQ(db.GroupCount(), 2u);
  EXPECT_NE(g1, g2);
  EXPECT_EQ(db.FindGroup("cg1")->name, "cg1");
  EXPECT_EQ(db.FindGroup("cg2")->name, "cg2");
}

} // namespace
