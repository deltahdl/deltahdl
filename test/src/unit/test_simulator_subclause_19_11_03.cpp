#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

CoverBin ValueBin(std::string name, int64_t value, uint64_t hits,
                  uint32_t at_least = 1) {
  CoverBin b;
  b.name = std::move(name);
  b.values = {value};
  b.hit_count = hits;
  b.at_least = at_least;
  return b;
}

CoverGroup GroupWithPoint(std::vector<CoverBin> bins, int32_t weight = 1) {
  CoverGroup g;
  CoverPoint cp;
  cp.name = "a";
  for (auto& b : bins) cp.bins.push_back(std::move(b));
  g.coverpoints.push_back(std::move(cp));
  g.options.weight = weight;
  return g;
}

TEST(TypeCoverage, WeightedAverageOfInstancesByOptionWeight) {
  CoverGroup a =
      GroupWithPoint({ValueBin("lo", 0, 1), ValueBin("hi", 1, 0)}, 1);
  CoverGroup b =
      GroupWithPoint({ValueBin("lo", 0, 1), ValueBin("hi", 1, 1)}, 3);
  std::vector<const CoverGroup*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, false), 87.5);
}

TEST(TypeCoverage, WeightedAverageZeroWeightIsZero) {
  CoverGroup a =
      GroupWithPoint({ValueBin("lo", 0, 1), ValueBin("hi", 1, 1)}, 0);
  std::vector<const CoverGroup*> insts = {&a};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, false), 0.0);
}

TEST(TypeCoverage, MergeUnionsBinsBySharedName) {
  CoverGroup a = GroupWithPoint({ValueBin("lo", 0, 1), ValueBin("hi", 1, 0)});
  CoverGroup b = GroupWithPoint({ValueBin("lo", 0, 0), ValueBin("hi", 1, 1)});
  std::vector<const CoverGroup*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, false), 50.0);
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, true), 100.0);
}

TEST(TypeCoverage, MergeSumsCountsOfOverlappingBins) {
  CoverGroup a = GroupWithPoint({ValueBin("lo", 0, 1, 2)});
  CoverGroup b = GroupWithPoint({ValueBin("lo", 0, 1, 2)});
  std::vector<const CoverGroup*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, false), 0.0);
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, true), 100.0);
}

TEST(TypeCoverage, MergeUnionExceedsIndividualInstancesFractionally) {
  CoverGroup a = GroupWithPoint({
      ValueBin("b0", 0, 1),
      ValueBin("b1", 1, 0),
      ValueBin("b2", 2, 0),
  });
  CoverGroup b = GroupWithPoint({
      ValueBin("b0", 0, 0),
      ValueBin("b1", 1, 1),
      ValueBin("b2", 2, 0),
  });
  std::vector<const CoverGroup*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, false), 100.0 / 3.0);
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, true),
                   100.0 * 2.0 / 3.0);
}

TEST(TypeCoverage, MergeKeepsDifferentlyNamedAutoBinsDistinct) {
  CoverGroup gv1 = GroupWithPoint({
      ValueBin("auto[0:1]", 0, 1),
      ValueBin("auto[2:3]", 2, 1),
      ValueBin("auto[4:5]", 4, 1),
      ValueBin("auto[6:7]", 6, 1),
  });
  CoverGroup gv2 = GroupWithPoint({
      ValueBin("auto[0:3]", 0, 0),
      ValueBin("auto[4:7]", 4, 0),
  });
  std::vector<const CoverGroup*> insts = {&gv1, &gv2};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, true),
                   100.0 * 4.0 / 6.0);
}

TEST(TypeCoverage, MergeWithNoParticipatingBinsIsFull) {
  CoverGroup g;
  std::vector<const CoverGroup*> insts = {&g};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, true), 100.0);
}

TEST(TypeCoverage, PointTypeCoverageWeightedByScopeWeight) {
  CoverPoint a;
  a.name = "a";
  a.weight = 1;
  a.bins = {ValueBin("lo", 0, 1), ValueBin("hi", 1, 0)};
  CoverPoint b;
  b.name = "a";
  b.weight = 3;
  b.bins = {ValueBin("lo", 0, 1), ValueBin("hi", 1, 1)};
  std::vector<const CoverPoint*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputePointTypeCoverage(insts, false), 87.5);
}

TEST(TypeCoverage, PointTypeCoverageMergeUnionsBins) {
  CoverPoint a;
  a.name = "a";
  a.bins = {ValueBin("lo", 0, 1), ValueBin("hi", 1, 0)};
  CoverPoint b;
  b.name = "a";
  b.bins = {ValueBin("lo", 0, 0), ValueBin("hi", 1, 1)};
  std::vector<const CoverPoint*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputePointTypeCoverage(insts, true), 100.0);
}

CrossCover CrossWithBins(std::vector<CrossBin> bins, int32_t weight = 1) {
  CrossCover c;
  c.name = "ab";
  c.coverpoint_names = {"a", "b"};
  c.bins = std::move(bins);
  c.option.weight = weight;
  return c;
}

CrossBin CrossBinNamed(std::string name, uint64_t hits, uint32_t at_least = 1) {
  CrossBin b;
  b.name = std::move(name);
  b.hit_count = hits;
  b.at_least = at_least;
  return b;
}

TEST(TypeCoverage, CrossTypeCoverageWeightedByScopeWeight) {
  CrossCover a = CrossWithBins(
      {CrossBinNamed("<a1,b1>", 1), CrossBinNamed("<a2,b2>", 0)}, 1);
  CrossCover b = CrossWithBins(
      {CrossBinNamed("<a1,b1>", 1), CrossBinNamed("<a2,b2>", 1)}, 3);
  std::vector<const CrossCover*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeCrossTypeCoverage(insts, false), 87.5);
}

TEST(TypeCoverage, CrossTypeCoverageMergeUnionsByProductName) {
  CrossCover a =
      CrossWithBins({CrossBinNamed("<a1,b1>", 1), CrossBinNamed("<a2,b2>", 0)});
  CrossCover b =
      CrossWithBins({CrossBinNamed("<a1,b1>", 0), CrossBinNamed("<a2,b2>", 1)});
  std::vector<const CrossCover*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeCrossTypeCoverage(insts, true), 100.0);
}

TEST(TypeCoverage, CovergroupMergeIncludesCrossBins) {
  CoverGroup a;
  a.crosses.push_back(CrossWithBins(
      {CrossBinNamed("<a1,b1>", 1), CrossBinNamed("<a2,b2>", 0)}));
  CoverGroup b;
  b.crosses.push_back(CrossWithBins(
      {CrossBinNamed("<a1,b1>", 0), CrossBinNamed("<a2,b2>", 1)}));
  std::vector<const CoverGroup*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, true), 100.0);
}

TEST(TypeCoverage, NoInstancesIsZero) {
  std::vector<const CoverGroup*> none;
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(none, false), 0.0);
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(none, true), 0.0);
  std::vector<const CoverPoint*> no_points;
  EXPECT_DOUBLE_EQ(CoverageDB::ComputePointTypeCoverage(no_points, false), 0.0);
  std::vector<const CrossCover*> no_crosses;
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeCrossTypeCoverage(no_crosses, true), 0.0);
}

}  // namespace
