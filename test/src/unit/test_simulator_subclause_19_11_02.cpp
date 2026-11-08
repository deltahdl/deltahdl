#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

CrossCover* BuildTwoByTwoCross(CoverageDB& db, CoverGroup*& out_group) {
  auto* g = db.CreateGroup("cg");
  auto* a = CoverageDB::AddCoverPoint(g, "a");
  CoverBin a0;
  a0.name = "a0";
  a0.values = {0};
  CoverageDB::AddBin(a, a0);
  CoverBin a1;
  a1.name = "a1";
  a1.values = {1};
  CoverageDB::AddBin(a, a1);

  auto* b = CoverageDB::AddCoverPoint(g, "b");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(b, b0);
  CoverBin b1;
  b1.name = "b1";
  b1.values = {1};
  CoverageDB::AddBin(b, b1);

  CrossCover cross;
  cross.name = "ab";
  cross.coverpoint_names = {"a", "b"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));
  CoverageDB::AutoCreateCrossBins(g, xc);

  out_group = g;
  return xc;
}

TEST(CrossCoverage, AutoBinCountIsProductMinusUserProducts) {
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({3, 2}, 2), 4u);
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({3, 2}, 0), 6u);
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({3, 0}, 0), 0u);
}

TEST(CrossCoverage, DenominatorIsAutoBinsPlusUserBins) {
  EXPECT_EQ(CoverageDB::CrossCoverageDenominator({3, 2}, 2, 1), 5u);
  EXPECT_EQ(CoverageDB::CrossCoverageDenominator({3, 2}, 0, 0), 6u);
}

TEST(CrossCoverage, OnlyCountingBinsContributeToUserBinCount) {
  EXPECT_TRUE(
      CoverageDB::CrossBinCountsTowardCoverage(CrossSampleOutcome::kCounted));
  EXPECT_FALSE(
      CoverageDB::CrossBinCountsTowardCoverage(CrossSampleOutcome::kIgnored));
  EXPECT_FALSE(CoverageDB::CrossBinCountsTowardCoverage(
      CrossSampleOutcome::kIllegalError));
}

TEST(CrossCoverage, AutoCreatedBinDenominatorMatchesFormula) {
  CoverageDB db;
  CoverGroup* g = nullptr;
  auto* xc = BuildTwoByTwoCross(db, g);

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetCrossCoverage(xc, covered, total);
  EXPECT_EQ(static_cast<uint64_t>(total),
            CoverageDB::CrossCoverageDenominator({2, 2}, 0, 0));
  EXPECT_EQ(total, 4);
}

TEST(CrossCoverage, CoverageIsCoveredOverDenominator) {
  CoverageDB db;
  CoverGroup* g = nullptr;
  auto* xc = BuildTwoByTwoCross(db, g);

  db.Sample(g, {{"a", 0}, {"b", 0}});
  db.Sample(g, {{"a", 1}, {"b", 1}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(xc), 50.0);
}

TEST(CrossCoverage, DenominatorZeroDetection) {
  CrossCover empty;
  empty.name = "empty";
  EXPECT_TRUE(CoverageDB::CrossCoverageDenominatorZero(&empty));

  CrossCover filled;
  filled.name = "filled";
  CrossBin bin;
  bin.name = "<0,0>";
  bin.value_sets = {{0}, {0}};
  filled.bins.push_back(bin);
  EXPECT_FALSE(CoverageDB::CrossCoverageDenominatorZero(&filled));
}

TEST(CrossCoverage, ZeroDenominatorNonzeroWeightReturnsZero) {
  CrossCover cross;
  cross.name = "x";
  cross.option.weight = 1;
  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&cross), 0.0);
}

TEST(CrossCoverage, ZeroDenominatorZeroWeightReturns100) {
  CrossCover cross;
  cross.name = "x";
  cross.option.weight = 0;
  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&cross), 100.0);
}

TEST(CrossCoverage, ZeroDenominatorTwoArgReportsZeroCounts) {
  CrossCover cross;
  cross.name = "x";

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetCrossCoverage(&cross, covered, total);
  EXPECT_EQ(covered, 0);
  EXPECT_EQ(total, 0);
}

TEST(CrossCoverage, TwoArgReportsCoveredAndDenominator) {
  CrossCover cross;
  cross.name = "x";
  CrossBin hit;
  hit.name = "<0,0>";
  hit.value_sets = {{0}, {0}};
  hit.hit_count = 1;
  cross.bins.push_back(hit);
  CrossBin miss;
  miss.name = "<1,1>";
  miss.value_sets = {{1}, {1}};
  cross.bins.push_back(miss);

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetCrossCoverage(&cross, covered, total);
  EXPECT_EQ(covered, 1);
  EXPECT_EQ(total, 2);
}

TEST(CrossCoverage, AllProductsTakenByUserBinsLeaveNoAutoBins) {
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({3, 2}, 6), 0u);
  EXPECT_EQ(CoverageDB::CrossCoverageDenominator({3, 2}, 6, 2), 2u);
}

TEST(CrossCoverage, UserProductsExceedingTotalClampToZero) {
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({3, 2}, 7), 0u);
}

TEST(CrossCoverage, ProductSpansAllCrossedCoverpoints) {
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({2, 2, 2}, 0), 8u);
  EXPECT_EQ(CoverageDB::CrossCoverageDenominator({2, 2, 2}, 0, 0), 8u);
}

TEST(CrossCoverage, UncoveredCrossWithZeroWeightReportsZero) {
  CrossCover cross;
  cross.name = "x";
  cross.option.weight = 0;
  CrossBin b0;
  b0.name = "<0,0>";
  b0.value_sets = {{0}, {0}};
  cross.bins.push_back(b0);
  CrossBin b1;
  b1.name = "<1,1>";
  b1.value_sets = {{1}, {1}};
  cross.bins.push_back(b1);

  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&cross), 0.0);
}

TEST(CrossCoverage, ZeroDenominatorCrossDroppedFromCovergroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* keep = CoverageDB::AddCoverPoint(g, "keep");
  CoverBin kb;
  kb.name = "b0";
  kb.values = {0};
  CoverageDB::AddBin(keep, kb);

  CrossCover empty;
  empty.name = "empty";
  empty.coverpoint_names = {"a", "b"};
  empty.option.weight = 1;
  CoverageDB::AddCross(g, std::move(empty));

  db.Sample(g, {{"keep", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 100.0);
}

}  // namespace
