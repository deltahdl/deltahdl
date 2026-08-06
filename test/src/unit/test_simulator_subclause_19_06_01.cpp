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

// Builds two coverpoints i and j, each with two single-value bins (value 0 and
// value 1), mirroring the "bins i[] = { [0:1] };" coverpoints of the §19.6.1
// example.
CoverPoint MakeTwoBinPoint(const std::string& name) {
  CoverPoint cp;
  cp.name = name;
  CoverBin b0;
  b0.name = name + "[0]";
  b0.values = {0};
  CoverBin b1;
  b1.name = name + "[1]";
  b1.values = {1};
  cp.bins = {b0, b1};
  return cp;
}

// binsof(cp) yields every bin of the coverpoint as a value set; binsof(cp.bin)
// yields only the named bin (LRM 19.6.1).
TEST(Coverage, BinsofYieldsCoverpointOrSingleBin) {
  CoverPoint i = MakeTwoBinPoint("i");

  auto all = CoverageDB::BinsofYield(&i);
  ASSERT_EQ(all.size(), 2u);
  EXPECT_EQ(all[0], (std::vector<int64_t>{0}));
  EXPECT_EQ(all[1], (std::vector<int64_t>{1}));

  auto one = CoverageDB::BinsofYield(&i, 0);
  ASSERT_EQ(one.size(), 1u);
  EXPECT_EQ(one[0], (std::vector<int64_t>{0}));
}

// "binsof(x) intersect {y}" keeps the bins whose values intersect y; the
// negated "! binsof(x) intersect {y}" keeps the bins that do not (LRM 19.6.1).
TEST(Coverage, IntersectSelectsBinsByValueOverlap) {
  CoverPoint i = MakeTwoBinPoint("i");
  auto bins = CoverageDB::BinsofYield(&i);

  auto included =
      CoverageDB::SelectBinsByIntersect(bins, {0}, /*negate=*/false);
  EXPECT_EQ(included, (std::vector<size_t>{0}));

  auto excluded = CoverageDB::SelectBinsByIntersect(bins, {0}, /*negate=*/true);
  EXPECT_EQ(excluded, (std::vector<size_t>{1}));
}

// The §19.6.1 cross x2 example: bins i_zero = binsof(i) intersect {0}. The
// user bin gathers the cross products <i[0],j[0]> and <i[0],j[1]>; the
// remaining products are retained as automatically generated bins because
// cross_retain_auto_bins defaults to true (LRM 19.6.1).
TEST(Coverage, UserCrossBinAndRetainedAutoBins) {
  CoverPoint i = MakeTwoBinPoint("i");
  std::vector<size_t> counts = {2, 2};

  auto i_bins = CoverageDB::BinsofYield(&i);
  auto i_sel = CoverageDB::SelectBinsByIntersect(i_bins, {0}, /*negate=*/false);
  auto user = CoverageDB::SelectProductsByPointBins(counts, /*point=*/0, i_sel);

  EXPECT_EQ(user, (std::vector<std::vector<size_t>>{{0, 0}, {0, 1}}));

  auto retained =
      CoverageDB::RetainedAutoCrossProducts(counts, user,
                                            /*retain_auto_bins=*/true);
  EXPECT_EQ(retained, (std::vector<std::vector<size_t>>{{1, 0}, {1, 1}}));

  // With cross_retain_auto_bins false, no automatic bins survive.
  auto none = CoverageDB::RetainedAutoCrossProducts(counts, user,
                                                    /*retain_auto_bins=*/false);
  EXPECT_TRUE(none.empty());
}

// Selected bins combine with the logical && and || operators (LRM 19.6.1).
TEST(Coverage, SelectionsCombineWithAndOr) {
  std::vector<size_t> counts = {2, 2};
  // binsof(i) intersect {0}  ->  products with i-bin 0
  auto sel_i0 = CoverageDB::SelectProductsByPointBins(counts, 0, {0});
  // binsof(j) intersect {1}  ->  products with j-bin 1
  auto sel_j1 = CoverageDB::SelectProductsByPointBins(counts, 1, {1});

  auto both = CoverageDB::AndCrossSelections(sel_i0, sel_j1);
  EXPECT_EQ(both, (std::vector<std::vector<size_t>>{{0, 1}}));

  auto either = CoverageDB::OrCrossSelections(sel_i0, sel_j1);
  EXPECT_EQ(either, (std::vector<std::vector<size_t>>{{0, 0}, {0, 1}, {1, 1}}));
}

// A cross coverage bin associates a count with a set of cross products; the
// count is incremented every time any of those products matches a sample
// (LRM 19.6.1).
TEST(Coverage, CrossBinCountsAnyMatchingProduct) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "i");
  CoverageDB::AddCoverPoint(g, "j");

  CrossCover cross;
  cross.name = "iXj";
  cross.coverpoint_names = {"i", "j"};
  // i_zero gathers <i[0],j[0]> and <i[0],j[1]>: i in {0}, j in {0,1}.
  CrossBin i_zero;
  i_zero.name = "i_zero";
  i_zero.value_sets = {{0}, {0, 1}};
  cross.bins.push_back(i_zero);
  CoverageDB::AddCross(g, cross);

  CrossBin* bin = &g->crosses[0].bins[0];
  db.Sample(g, {{"i", 0}, {"j", 0}});  // matches <i[0],j[0]>
  EXPECT_EQ(bin->hit_count, 1u);
  db.Sample(g, {{"i", 0}, {"j", 1}});  // matches <i[0],j[1]>
  EXPECT_EQ(bin->hit_count, 2u);
  db.Sample(g, {{"i", 1}, {"j", 0}});  // matches neither product
  EXPECT_EQ(bin->hit_count, 2u);
}

// binsof on an absent coverpoint, a bin index past the end, or a coverpoint
// with no bins yields nothing (LRM 19.6.1).
TEST(Coverage, BinsofYieldHandlesEmptyAndOutOfRange) {
  EXPECT_TRUE(CoverageDB::BinsofYield(nullptr).empty());

  CoverPoint i = MakeTwoBinPoint("i");
  EXPECT_TRUE(
      CoverageDB::BinsofYield(&i, 2).empty());  // only bins 0 and 1 exist

  CoverPoint empty;
  empty.name = "empty";
  EXPECT_TRUE(CoverageDB::BinsofYield(&empty).empty());
}

// intersect selects a bin when any of its values overlaps the desired set, even
// for a multi-value bin; the negated form drops exactly the overlapping bins.
// An empty desired set intersects no bin (LRM 19.6.1).
TEST(Coverage, IntersectMatchesOnAnyValueOverlap) {
  std::vector<std::vector<int64_t>> bins = {{2, 3, 4}, {6, 7}};

  // Bin 0 shares the value 4 with {4,5}; bin 1 shares nothing.
  auto included =
      CoverageDB::SelectBinsByIntersect(bins, {4, 5}, /*negate=*/false);
  EXPECT_EQ(included, (std::vector<size_t>{0}));

  auto excluded =
      CoverageDB::SelectBinsByIntersect(bins, {4, 5}, /*negate=*/true);
  EXPECT_EQ(excluded, (std::vector<size_t>{1}));

  EXPECT_TRUE(
      CoverageDB::SelectBinsByIntersect(bins, {}, /*negate=*/false).empty());
  EXPECT_EQ(CoverageDB::SelectBinsByIntersect(bins, {}, /*negate=*/true),
            (std::vector<size_t>{0, 1}));
}

// A cross enumerates no products when one of its coverpoints contributes no
// bins, so there is nothing to group into a cross bin (LRM 19.6.1).
TEST(Coverage, NoCrossProductsWhenACoverpointHasNoBins) {
  EXPECT_TRUE(CoverageDB::EnumerateCrossProducts({2, 0}).empty());
}

// A select expression that picks no bin of a coverpoint, and the && of two
// disjoint selections, both denote no cross products (LRM 19.6.1).
TEST(Coverage, EmptyAndDisjointSelectionsDenoteNoProducts) {
  std::vector<size_t> counts = {2, 2};

  EXPECT_TRUE(CoverageDB::SelectProductsByPointBins(counts, 0, {}).empty());

  auto i0 =
      CoverageDB::SelectProductsByPointBins(counts, 0, {0});  // {0,0},{0,1}
  auto i1 =
      CoverageDB::SelectProductsByPointBins(counts, 0, {1});  // {1,0},{1,1}
  EXPECT_TRUE(CoverageDB::AndCrossSelections(i0, i1).empty());
}

// When user-defined cross bins already cover every cross product, no
// automatically generated bins are retained even with cross_retain_auto_bins at
// its default of true (LRM 19.6.1).
TEST(Coverage, NoAutoBinsRetainedWhenUserBinsCoverAll) {
  std::vector<size_t> counts = {2, 2};
  auto all = CoverageDB::EnumerateCrossProducts(counts);
  ASSERT_EQ(all.size(), 4u);

  auto retained =
      CoverageDB::RetainedAutoCrossProducts(counts, all,
                                            /*retain_auto_bins=*/true);
  EXPECT_TRUE(retained.empty());
}

}  // namespace
