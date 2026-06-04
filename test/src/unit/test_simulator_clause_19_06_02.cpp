#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

CoverBin MakeValueBin(const std::string& name, std::vector<int64_t> values) {
  CoverBin b;
  b.name = name;
  b.values = std::move(values);
  return b;
}

// LRM 19.6.2: all cross products that satisfy an ignore_bins select expression
// are excluded from coverage. This mirrors the clause example
//   cross a, b { ignore_bins ignore = binsof(a) intersect { 5, [1:3] }; }
// the select expression is evaluated to its cross products by the LRM 19.6.1
// machinery and ExcludeIgnoredCrossProducts removes them from the cross's
// products.
TEST(Coverage, IgnoreBinsExcludesSelectedCrossProducts) {
  // Coverpoint a has four value bins; coverpoint b has two bins.
  CoverPoint a;
  a.name = "a";
  a.bins = {MakeValueBin("a0", {0}), MakeValueBin("a1", {2}),
            MakeValueBin("a2", {5}), MakeValueBin("a3", {9})};

  std::vector<size_t> per_point_bin_counts = {4, 2};
  auto all = CoverageDB::EnumerateCrossProducts(per_point_bin_counts);
  ASSERT_EQ(all.size(), 8u);

  // binsof(a) intersect { 5, [1:3] } -> a's bins whose values intersect
  // {5,1,2,3}: a1 (value 2) and a2 (value 5).
  auto a_bins = CoverageDB::BinsofYield(&a);
  auto selected_a =
      CoverageDB::SelectBinsByIntersect(a_bins, {5, 1, 2, 3}, /*negate=*/false);
  EXPECT_EQ(selected_a, (std::vector<size_t>{1, 2}));

  // The ignore select expression names one coverpoint, so b ranges over all of
  // its bins; the ignored cross products are every <a in {1,2}, any b>.
  auto ignored = CoverageDB::SelectProductsByPointBins(per_point_bin_counts,
                                                       /*point=*/0, selected_a);
  EXPECT_EQ(ignored.size(), 4u);

  auto kept = CoverageDB::ExcludeIgnoredCrossProducts(all, ignored);
  std::vector<std::vector<size_t>> expected = {
      {0, 0}, {0, 1}, {3, 0}, {3, 1}};
  EXPECT_EQ(kept, expected);
}

// An ignore_bins select expression that selects nothing leaves the cross
// products untouched (LRM 19.6.2).
TEST(Coverage, EmptyIgnoreSelectionLeavesProductsIntact) {
  auto all = CoverageDB::EnumerateCrossProducts({2, 2});
  ASSERT_EQ(all.size(), 4u);
  auto kept = CoverageDB::ExcludeIgnoredCrossProducts(all, {});
  EXPECT_EQ(kept, all);
}

// An ignore_bins select expression that selects every cross product excludes the
// whole cross from coverage (LRM 19.6.2).
TEST(Coverage, IgnoringAllProductsExcludesEverything) {
  auto all = CoverageDB::EnumerateCrossProducts({2, 2});
  auto kept = CoverageDB::ExcludeIgnoredCrossProducts(all, all);
  EXPECT_TRUE(kept.empty());
}

// LRM 19.6.2: ignored cross products are excluded even when included in another
// cross coverage bin of the enclosing cross. A user-defined cross bin's product
// set still loses any ignored product.
TEST(Coverage, IgnoredProductExcludedFromOtherCrossBin) {
  // A user-defined cross bin that happens to include an ignored product (1,0)
  // alongside a non-ignored one (0,0).
  std::vector<std::vector<size_t>> user_bin = {{1, 0}, {0, 0}};
  std::vector<std::vector<size_t>> ignored = {{1, 0}, {1, 1}};

  auto effective = CoverageDB::ExcludeIgnoredCrossProducts(user_bin, ignored);
  std::vector<std::vector<size_t>> expected = {{0, 0}};
  EXPECT_EQ(effective, expected);
}

// The precedence is unconditional: an ignored cross product is never retained,
// whether or not another cross bin also includes it (LRM 19.6.2).
TEST(Coverage, IgnoredProductNeverRetained) {
  EXPECT_FALSE(CoverageDB::IgnoredCrossProductRetained(
      /*also_in_other_cross_bin=*/true));
  EXPECT_FALSE(CoverageDB::IgnoredCrossProductRetained(
      /*also_in_other_cross_bin=*/false));
}

}
