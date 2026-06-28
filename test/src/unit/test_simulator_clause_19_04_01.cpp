#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// §19.4.1: when a derived covergroup defines a coverpoint whose name matches a
// base coverpoint, that base coverpoint no longer contributes to the coverage
// computation. Here the base covergroup has an uncovered coverpoint "a" and a
// covered coverpoint "b" (50% before). Overriding "a" drops it from the
// average, leaving only "b" — coverage becomes 100%.
TEST(Coverage, DerivedOverridesBaseCoverpoint) {
  CoverageDB db;
  CoverGroup* base = db.CreateGroup("base_cg");

  CoverPoint* a = CoverageDB::AddCoverPoint(base, "a");
  CoverBin a_bin;
  a_bin.name = "a0";
  a_bin.values = {0};   // §19.5: a coverpoint bin holds a value set
  a_bin.hit_count = 0;  // uncovered
  CoverageDB::AddBin(a, a_bin);

  CoverPoint* b = CoverageDB::AddCoverPoint(base, "b");
  CoverBin b_bin;
  b_bin.name = "b0";
  b_bin.values = {1};   // §19.5: a coverpoint bin holds a value set
  b_bin.hit_count = 1;  // covered
  CoverageDB::AddBin(b, b_bin);

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(base), 50.0);

  CoverageDB::ApplyDerivedCoverpointOverrides(base, {"a"});
  EXPECT_TRUE(base->coverpoints[0].excluded_from_coverage);
  EXPECT_FALSE(base->coverpoints[1].excluded_from_coverage);

  // The overridden coverpoint no longer contributes; only "b" remains.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(base), 100.0);
}

// §19.4.1: even when a base coverpoint no longer contributes, a cross in the
// base covergroup that includes that coverpoint still contributes to the
// computation, provided the derived covergroup does not define a cross with the
// same name. Overriding coverpoint "a" excludes it, but base cross "x1" keeps
// contributing.
TEST(Coverage, BaseCrossStillContributesAfterCoverpointOverride) {
  CoverageDB db;
  CoverGroup* base = db.CreateGroup("base_cg");

  CoverPoint* a = CoverageDB::AddCoverPoint(base, "a");
  CoverBin a_bin;
  a_bin.name = "a0";
  a_bin.hit_count = 0;  // uncovered
  CoverageDB::AddBin(a, a_bin);

  CrossCover cross;
  cross.name = "x1";
  cross.coverpoint_names = {"a"};
  CrossBin xb;
  xb.name = "xb0";
  xb.hit_count = 1;  // covered
  cross.bins.push_back(xb);
  CoverageDB::AddCross(base, cross);

  CoverageDB::ApplyDerivedCoverpointOverrides(base, {"a"});
  CoverageDB::ApplyDerivedCrossOverrides(base, /*derived_cross_names=*/{});

  EXPECT_TRUE(base->coverpoints[0].excluded_from_coverage);
  EXPECT_FALSE(base->crosses[0].excluded_from_coverage);

  // The overridden coverpoint is gone, but the base cross still contributes.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(base), 100.0);
}

// §19.4.1: a base cross stops contributing when, and only when, the derived
// covergroup defines a cross with the same name.
TEST(Coverage, DerivedCrossWithSameNameOverridesBaseCross) {
  CoverageDB db;
  CoverGroup* base = db.CreateGroup("base_cg");

  CrossCover cross;
  cross.name = "x1";
  CrossBin xb;
  xb.name = "xb0";
  xb.hit_count = 1;
  cross.bins.push_back(xb);
  CoverageDB::AddCross(base, cross);

  CoverageDB::ApplyDerivedCrossOverrides(base, /*derived_cross_names=*/{"x1"});
  EXPECT_TRUE(base->crosses[0].excluded_from_coverage);
}

// §19.4.1: for get_coverage(), a derived covergroup and its base covergroup are
// separate types, so no aggregation occurs across them. Only instances naming
// the same covergroup type aggregate.
TEST(Coverage, DerivedAndBaseAreSeparateTypesForGetCoverage) {
  EXPECT_FALSE(CoverageDB::CovergroupTypesAggregate("base_cg", "derived_cg"));
  EXPECT_TRUE(CoverageDB::CovergroupTypesAggregate("base_cg", "base_cg"));
}

}  // namespace
