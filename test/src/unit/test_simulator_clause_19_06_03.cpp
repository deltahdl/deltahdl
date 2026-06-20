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

// LRM 19.6.3: all cross products that satisfy an illegal_bins select expression
// are excluded from coverage. This mirrors the clause example
//   cross x, y { illegal_bins illegal = binsof(y) intersect {bad}; }
// the select expression is evaluated to its cross products by the LRM 19.6.1
// machinery and ExcludeIllegalCrossProducts removes them from the cross's
// products, exactly as the ignore_bins case does.
TEST(Coverage, IllegalBinsExcludesSelectedCrossProducts) {
  // Coverpoint x has two value bins; coverpoint y has three bins.
  CoverPoint y;
  y.name = "y";
  y.bins = {MakeValueBin("y0", {0}), MakeValueBin("y1", {7}),
            MakeValueBin("y2", {9})};

  std::vector<size_t> per_point_bin_counts = {2, 3};
  auto all = CoverageDB::EnumerateCrossProducts(per_point_bin_counts);
  ASSERT_EQ(all.size(), 6u);

  // binsof(y) intersect {bad} with bad == 7 -> y's bin whose value intersects
  // {7}: y1.
  auto y_bins = CoverageDB::BinsofYield(&y);
  auto selected_y =
      CoverageDB::SelectBinsByIntersect(y_bins, {7}, /*negate=*/false);
  EXPECT_EQ(selected_y, (std::vector<size_t>{1}));

  // The illegal select expression names only coverpoint y, so x ranges over all
  // of its bins; the illegal cross products are every <any x, y == y1>.
  auto illegal = CoverageDB::SelectProductsByPointBins(per_point_bin_counts,
                                                       /*point=*/1, selected_y);
  EXPECT_EQ(illegal.size(), 2u);

  auto kept = CoverageDB::ExcludeIllegalCrossProducts(all, illegal);
  std::vector<std::vector<size_t>> expected = {{0, 0}, {0, 2}, {1, 0}, {1, 2}};
  EXPECT_EQ(kept, expected);
}

// LRM 19.6.3: a sampled cross product that satisfies the illegal_bins select
// expression raises a run-time error and counts toward no coverage bin.
TEST(Coverage, SampledIllegalCrossProductRaisesError) {
  std::vector<std::vector<size_t>> illegal = {{1, 0}, {1, 1}};
  std::vector<std::vector<size_t>> ignored = {};

  EXPECT_EQ(CoverageDB::ClassifyCrossSample({1, 0}, illegal, ignored,
                                            /*also_in_other_cross_bin=*/false),
            CrossSampleOutcome::kIllegalError);
  // A product not selected by illegal_bins is counted normally.
  EXPECT_EQ(CoverageDB::ClassifyCrossSample({0, 0}, illegal, ignored,
                                            /*also_in_other_cross_bin=*/false),
            CrossSampleOutcome::kCounted);
}

// LRM 19.6.3: illegal cross products take precedence. A product that is both
// illegal and explicitly ignored by an ignore_bins select expression still
// raises the run-time error.
TEST(Coverage, IllegalTakesPrecedenceOverIgnore) {
  std::vector<std::vector<size_t>> illegal = {{1, 0}};
  std::vector<std::vector<size_t>> ignored = {{1, 0}};

  EXPECT_EQ(CoverageDB::ClassifyCrossSample({1, 0}, illegal, ignored,
                                            /*also_in_other_cross_bin=*/false),
            CrossSampleOutcome::kIllegalError);
}

// LRM 19.6.3: illegal cross products take precedence over inclusion in another
// cross coverage bin of the enclosing cross. The run-time error is still
// raised.
TEST(Coverage, IllegalTakesPrecedenceOverOtherCrossBin) {
  std::vector<std::vector<size_t>> illegal = {{0, 1}};
  std::vector<std::vector<size_t>> ignored = {};

  EXPECT_EQ(CoverageDB::ClassifyCrossSample({0, 1}, illegal, ignored,
                                            /*also_in_other_cross_bin=*/true),
            CrossSampleOutcome::kIllegalError);
}

// A non-illegal product that is named only by an ignore_bins select expression
// is excluded from coverage but raises no error (LRM 19.6.3 vs 19.6.2).
TEST(Coverage, IgnoredNonIllegalProductIsNotAnError) {
  std::vector<std::vector<size_t>> illegal = {{1, 0}};
  std::vector<std::vector<size_t>> ignored = {{0, 1}};

  EXPECT_EQ(CoverageDB::ClassifyCrossSample({0, 1}, illegal, ignored,
                                            /*also_in_other_cross_bin=*/false),
            CrossSampleOutcome::kIgnored);
}

// An illegal_bins select expression that selects nothing leaves the cross
// products untouched, and only the matching products are excluded; a near-miss
// product that differs in a single coverpoint index is kept (LRM 19.6.3).
TEST(Coverage, OnlyMatchingIllegalProductsAreExcluded) {
  std::vector<std::vector<size_t>> products = {{0, 0}, {0, 1}, {1, 0}};
  // {1,0} is present and is dropped; {0,2} differs from {0,1} in one index and
  // {2,2} is absent entirely — neither disturbs the surviving products.
  std::vector<std::vector<size_t>> illegal = {{1, 0}, {0, 2}, {2, 2}};

  auto kept = CoverageDB::ExcludeIllegalCrossProducts(products, illegal);
  std::vector<std::vector<size_t>> expected = {{0, 0}, {0, 1}};
  EXPECT_EQ(kept, expected);

  EXPECT_EQ(CoverageDB::ExcludeIllegalCrossProducts(products, {}), products);
}

// Edge case for C1a: an illegal_bins select expression that selects every cross
// product excludes the whole cross from coverage (LRM 19.6.3).
TEST(Coverage, IllegalBinsCanExcludeEveryCrossProduct) {
  auto all = CoverageDB::EnumerateCrossProducts({2, 2});
  ASSERT_EQ(all.size(), 4u);
  auto kept = CoverageDB::ExcludeIllegalCrossProducts(all, all);
  EXPECT_TRUE(kept.empty());
}

// Edge case for C2: precedence is unconditional. A product that is illegal and
// at the same time named by an ignore_bins select expression and included in
// another cross coverage bin still raises the run-time error (LRM 19.6.3).
TEST(Coverage, IllegalPrecedenceHoldsWhenAlsoIgnoredAndInOtherCrossBin) {
  std::vector<std::vector<size_t>> illegal = {{1, 1}};
  std::vector<std::vector<size_t>> ignored = {{1, 1}};

  EXPECT_EQ(CoverageDB::ClassifyCrossSample({1, 1}, illegal, ignored,
                                            /*also_in_other_cross_bin=*/true),
            CrossSampleOutcome::kIllegalError);
}

}  // namespace
