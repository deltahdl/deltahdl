#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// Builds a value bin with the given name, a single distinguishing value (so the
// bin participates in coverage), and the supplied hit count and at_least.
CoverBin ValueBin(std::string name, int64_t value, uint64_t hits,
                  uint32_t at_least = 1) {
  CoverBin b;
  b.name = std::move(name);
  b.values = {value};
  b.hit_count = hits;
  b.at_least = at_least;
  return b;
}

// A covergroup type instance with a single coverpoint named "a" holding the
// given bins, plus the covergroup-scope option.weight used by the type-coverage
// weighted average.
CoverGroup GroupWithPoint(std::vector<CoverBin> bins, uint32_t weight = 1) {
  CoverGroup g;
  CoverPoint cp;
  cp.name = "a";
  cp.bins = std::move(bins);
  g.coverpoints.push_back(std::move(cp));
  g.options.weight = weight;
  return g;
}

// LRM 19.11.3: with merge_instances false, the covergroup type coverage is the
// weighted average of the per-instance coverage, each instance weighted by its
// own option.weight. Instance A is 50% covered (1 of 2 bins) with weight 1 and
// instance B is 100% covered with weight 3, so the type coverage is
// (50*1 + 100*3) / 4 = 87.5.
TEST(TypeCoverage, WeightedAverageOfInstancesByOptionWeight) {
  CoverGroup a = GroupWithPoint({ValueBin("lo", 0, 1), ValueBin("hi", 1, 0)},
                                /*weight=*/1);
  CoverGroup b = GroupWithPoint({ValueBin("lo", 0, 1), ValueBin("hi", 1, 1)},
                                /*weight=*/3);
  std::vector<const CoverGroup*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/false), 87.5);
}

// LRM 19.11.3: when every instance weight is zero the weighted-average
// denominator is zero and the type coverage is reported as 0.
TEST(TypeCoverage, WeightedAverageZeroWeightIsZero) {
  CoverGroup a = GroupWithPoint({ValueBin("lo", 0, 1), ValueBin("hi", 1, 1)},
                                /*weight=*/0);
  std::vector<const CoverGroup*> insts = {&a};
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/false), 0.0);
}

// LRM 19.11.3: with merge_instances true, the bins of every instance are
// unioned. Bins that share a name overlap, so a bin covered in any instance is
// covered in the union. Here each instance covers a different bin yet shares
// the bin names, so the union covers both bins (100%) while neither instance
// alone reaches it (50%).
TEST(TypeCoverage, MergeUnionsBinsBySharedName) {
  CoverGroup a = GroupWithPoint({ValueBin("lo", 0, 1), ValueBin("hi", 1, 0)});
  CoverGroup b = GroupWithPoint({ValueBin("lo", 0, 0), ValueBin("hi", 1, 1)});
  std::vector<const CoverGroup*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/false), 50.0);
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/true), 100.0);
}

// LRM 19.11.3: the cumulative count of an overlapping (same-named) bin is the
// sum of its counts in every instance containing it. With at_least = 2 a single
// hit in each of two instances sums to 2 and covers the merged bin, even though
// neither instance reaches the threshold on its own.
TEST(TypeCoverage, MergeSumsCountsOfOverlappingBins) {
  CoverGroup a = GroupWithPoint({ValueBin("lo", 0, 1, /*at_least=*/2)});
  CoverGroup b = GroupWithPoint({ValueBin("lo", 0, 1, /*at_least=*/2)});
  std::vector<const CoverGroup*> insts = {&a, &b};
  // Neither instance covers the bin on its own.
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/false), 0.0);
  // The summed count reaches the threshold in the union.
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/true), 100.0);
}

// LRM 19.11.3: when same-named bins overlap across instances, a bin covered in
// any instance is covered in the union, while the union denominator still
// counts each distinct bin name once. This mirrors the standard's "gt" example:
// two instances share the bins b0, b1, b2; one instance covers b0 and the other
// covers b1, leaving b2 uncovered everywhere. The merged coverage is therefore
// 2/3, strictly more than either instance alone (each covers only 1/3).
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
  // Each instance alone covers only one of its three bins.
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/false),
      100.0 / 3.0);
  // The union covers b0 and b1 but not b2: two of three distinct bins.
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/true),
      100.0 * 2.0 / 3.0);
}

// LRM 19.11.3: bins with distinct names are distinct members of the union, so
// instances whose bin layouts differ enlarge the union rather than collapse.
// This mirrors the standard's "ga" example, where two instances with different
// auto_bin_max have differently named auto bins that do not overlap. Instance
// gv1 has four auto bins (all covered) and gv2 has two differently named auto
// bins (uncovered); the union therefore has six bins, four covered: 4/6.
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
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/true),
      100.0 * 4.0 / 6.0);
}

// LRM 19.11.3: a merged union containing no participating bins reports full
// coverage (a zero denominator).
TEST(TypeCoverage, MergeWithNoParticipatingBinsIsFull) {
  CoverGroup g;  // no coverpoints, no crosses
  std::vector<const CoverGroup*> insts = {&g};
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/true), 100.0);
}

// LRM 19.11.3: the type coverage of a coverpoint is its coverage in each
// instance, weighted by the coverpoint-scope option.weight. Coverpoint instance
// A is 50% with weight 1, B is 100% with weight 3: (50 + 300) / 4 = 87.5.
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
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputePointTypeCoverage(insts, /*merge_instances=*/false),
      87.5);
}

// LRM 19.11.3: with merge, a coverpoint's type coverage unions its bins by name
// across instances; each instance here covers one of the two shared bins.
TEST(TypeCoverage, PointTypeCoverageMergeUnionsBins) {
  CoverPoint a;
  a.name = "a";
  a.bins = {ValueBin("lo", 0, 1), ValueBin("hi", 1, 0)};
  CoverPoint b;
  b.name = "a";
  b.bins = {ValueBin("lo", 0, 0), ValueBin("hi", 1, 1)};
  std::vector<const CoverPoint*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputePointTypeCoverage(insts, /*merge_instances=*/true),
      100.0);
}

// Builds a cross named "ab" with the given cross bins and cross-scope weight.
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

// LRM 19.11.3: the type coverage of a cross is its coverage in each instance,
// weighted by the cross-scope option.weight. Cross instance A is 50% with
// weight 1, B is 100% with weight 3: (50 + 300) / 4 = 87.5.
TEST(TypeCoverage, CrossTypeCoverageWeightedByScopeWeight) {
  CrossCover a = CrossWithBins(
      {CrossBinNamed("<a1,b1>", 1), CrossBinNamed("<a2,b2>", 0)}, 1);
  CrossCover b = CrossWithBins(
      {CrossBinNamed("<a1,b1>", 1), CrossBinNamed("<a2,b2>", 1)}, 3);
  std::vector<const CrossCover*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeCrossTypeCoverage(insts, /*merge_instances=*/false),
      87.5);
}

// LRM 19.11.3: with merge, automatically created cross bins are unioned by
// their cross-product bin name; instances sharing the same cross product bin
// name overlap. Each instance covers a different cross bin, so the union covers
// both.
TEST(TypeCoverage, CrossTypeCoverageMergeUnionsByProductName) {
  CrossCover a =
      CrossWithBins({CrossBinNamed("<a1,b1>", 1), CrossBinNamed("<a2,b2>", 0)});
  CrossCover b =
      CrossWithBins({CrossBinNamed("<a1,b1>", 0), CrossBinNamed("<a2,b2>", 1)});
  std::vector<const CrossCover*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeCrossTypeCoverage(insts, /*merge_instances=*/true),
      100.0);
}

// LRM 19.11.3: the covergroup-level merge unions cross bins too, keyed by their
// cross-product name. Two instances each carrying the cross "ab" with two cross
// bins cover one bin each, so the merged covergroup type coverage is 100%.
TEST(TypeCoverage, CovergroupMergeIncludesCrossBins) {
  CoverGroup a;
  a.crosses.push_back(CrossWithBins(
      {CrossBinNamed("<a1,b1>", 1), CrossBinNamed("<a2,b2>", 0)}));
  CoverGroup b;
  b.crosses.push_back(CrossWithBins(
      {CrossBinNamed("<a1,b1>", 0), CrossBinNamed("<a2,b2>", 1)}));
  std::vector<const CoverGroup*> insts = {&a, &b};
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/true), 100.0);
}

// LRM 19.11.3: type coverage of an empty instance set is reported as 0 for both
// computation modes.
TEST(TypeCoverage, NoInstancesIsZero) {
  std::vector<const CoverGroup*> none;
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(none, /*merge_instances=*/false), 0.0);
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(none, /*merge_instances=*/true), 0.0);
  std::vector<const CoverPoint*> no_points;
  EXPECT_DOUBLE_EQ(CoverageDB::ComputePointTypeCoverage(no_points, false), 0.0);
  std::vector<const CrossCover*> no_crosses;
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeCrossTypeCoverage(no_crosses, true), 0.0);
}

}  // namespace
