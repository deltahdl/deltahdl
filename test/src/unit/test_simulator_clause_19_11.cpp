#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, AutoBinSampleAndCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 3);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  db.Sample(g, {{"x", 2}});
  db.Sample(g, {{"x", 3}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(Coverage, EmptyGroupCoverageIsZero) {
  CoverageDB db;
  auto* g = db.CreateGroup("empty");
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 0.0);
}

TEST(Coverage, PointCoverageWithNoBinsIs100) {
  CoverPoint cp;
  cp.name = "empty_cp";
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(&cp), 100.0);
}

// LRM 19.11: Cg is the weighted average Σ(Wi×Ci)/Σ(Wi) of its items, so an
// item's weight scales its contribution. The fully covered item has weight 3
// and the empty item weight 1, giving (3*100 + 1*0)/4 = 75, not the unweighted
// 50.
TEST(Coverage, CovergroupCoverageIsItemWeightedAverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* full = CoverageDB::AddCoverPoint(g, "full");
  full->weight = 3;
  CoverBin fb;
  fb.name = "b0";
  fb.values = {0};
  CoverageDB::AddBin(full, fb);

  auto* empty = CoverageDB::AddCoverPoint(g, "empty");
  empty->weight = 1;
  CoverBin eb;
  eb.name = "b0";
  eb.values = {0};
  CoverageDB::AddBin(empty, eb);

  db.Sample(g, {{"full", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 75.0);
}

// LRM 19.11: the items averaged in Cg are the covergroup's coverpoints AND its
// crosses. A covered cross of weight 3 and an uncovered coverpoint of weight 1
// give (3*100 + 1*0)/4 = 75, so the cross contributes to the weighted average
// like any other item.
TEST(Coverage, CovergroupCoverageWeightsCrossItems) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* cp = CoverageDB::AddCoverPoint(g, "z");
  cp->weight = 1;
  CoverBin zb;
  zb.name = "b0";
  zb.values = {0};
  CoverageDB::AddBin(cp, zb);

  CrossCover cross;
  cross.name = "xy";
  cross.coverpoint_names = {"x", "y"};
  cross.option.weight = 3;
  CrossBin cb;
  cb.name = "<0,0>";
  cb.value_sets = {{0}, {0}};
  cross.bins.push_back(cb);
  CoverageDB::AddCross(g, std::move(cross));

  // Covers the cross bin; the coverpoint "z" is never sampled, so it stays 0%.
  db.Sample(g, {{"x", 0}, {"y", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 75.0);
}

// LRM 19.11: an item excluded by its own coverage rules is dropped from both
// the numerator and the denominator. With the uncovered item excluded, Cg is
// the surviving item's 100% rather than the 50% it would average to.
TEST(Coverage, ExcludedItemDropsFromBothNumeratorAndDenominator) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* keep = CoverageDB::AddCoverPoint(g, "keep");
  CoverBin kb;
  kb.name = "b0";
  kb.values = {0};
  CoverageDB::AddBin(keep, kb);

  auto* drop = CoverageDB::AddCoverPoint(g, "drop");
  CoverBin db0;
  db0.name = "b0";
  db0.values = {0};
  CoverageDB::AddBin(drop, db0);
  drop->excluded_from_coverage = true;

  db.Sample(g, {{"keep", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 100.0);
}

// LRM 19.11: the covergroup denominator Σ Wi is zero when every item weight is
// zero.
TEST(Coverage, AllItemWeightsZeroMakesDenominatorZero) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->weight = 0;
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});

  EXPECT_TRUE(CoverageDB::CovergroupCoverageDenominatorZero(g));
}

// LRM 19.11: the covergroup denominator is also zero when every item is
// excluded by its own coverage rules, since each excluded item contributes no
// weight.
TEST(Coverage, AllItemsExcludedMakesDenominatorZero) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);
  cp->excluded_from_coverage = true;

  db.Sample(g, {{"x", 0}});

  EXPECT_TRUE(CoverageDB::CovergroupCoverageDenominatorZero(g));
}

// LRM 19.11: the covergroup denominator is also zero when the covergroup
// contains no coverpoints or crosses at all.
TEST(Coverage, NoItemsMakesDenominatorZero) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  EXPECT_TRUE(CoverageDB::CovergroupCoverageDenominatorZero(g));
}

// LRM 19.11: a zero denominator with a zero covergroup weight reports a
// coverage of 100.0 (an empty covergroup whose weight is zero).
TEST(Coverage, ZeroDenominatorZeroWeightCovergroupReports100) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.weight = 0;

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 100.0);
}

// LRM 19.11: when get_coverage is called with two arguments and the covergroup
// denominator is zero, zero is assigned to both the numerator and the
// denominator, even though the sole item has a covered bin.
TEST(Coverage, ZeroDenominatorTwoArgFormReportsZeroCounts) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->weight = 0;
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetCoverage(g, covered, total);
  EXPECT_EQ(covered, 0);
  EXPECT_EQ(total, 0);
}

// LRM 19.11: $get_coverage returns 100.0 for a design that has no covergroup
// instances.
TEST(Coverage, OverallCoverageNoInstancesIs100) {
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeOverallCoverage({}), 100.0);
}

// LRM 19.11: a covergroup whose own denominator is zero does not contribute to
// the overall score. The empty instance is skipped, so the overall coverage is
// the covered instance's 100%, not a 50% average with the empty one.
TEST(Coverage, OverallCoverageSkipsZeroDenominatorInstances) {
  CoverageDB db;
  auto* good = db.CreateGroup("good");
  auto* cp = CoverageDB::AddCoverPoint(good, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);
  db.Sample(good, {{"x", 0}});

  auto* empty = db.CreateGroup("empty");

  EXPECT_DOUBLE_EQ(CoverageDB::ComputeOverallCoverage({good, empty}), 100.0);
}

// LRM 19.11: $get_coverage returns 100.0 for a design in which every covergroup
// has a weight of zero, even when an instance has covered bins.
TEST(Coverage, OverallCoverageAllZeroWeightIs100) {
  CoverageDB db;
  auto* g = db.CreateGroup("g");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);
  db.Sample(g, {{"x", 0}});
  g->options.weight = 0;

  EXPECT_DOUBLE_EQ(CoverageDB::ComputeOverallCoverage({g}), 100.0);
}

}  // namespace
