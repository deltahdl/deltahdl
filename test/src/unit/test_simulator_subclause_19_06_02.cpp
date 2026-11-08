#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

CoverBin MakeValueBin(const std::string& name, std::vector<int64_t> values) {
  CoverBin b;
  b.name = name;
  b.values = std::move(values);
  return b;
}

TEST(Coverage, IgnoreBinsExcludesSelectedCrossProducts) {
  CoverPoint a;
  a.name = "a";
  a.bins = {MakeValueBin("a0", {0}), MakeValueBin("a1", {2}),
            MakeValueBin("a2", {5}), MakeValueBin("a3", {9})};

  std::vector<size_t> per_point_bin_counts = {4, 2};
  auto all = CoverageDB::EnumerateCrossProducts(per_point_bin_counts);
  ASSERT_EQ(all.size(), 8u);

  auto a_bins = CoverageDB::BinsofYield(&a);
  auto selected_a =
      CoverageDB::SelectBinsByIntersect(a_bins, {5, 1, 2, 3}, false);
  EXPECT_EQ(selected_a, (std::vector<size_t>{1, 2}));

  auto ignored = CoverageDB::SelectProductsByPointBins(per_point_bin_counts, 0,
                                                       selected_a);
  EXPECT_EQ(ignored.size(), 4u);

  auto kept = CoverageDB::ExcludeIgnoredCrossProducts(all, ignored);
  std::vector<std::vector<size_t>> expected = {{0, 0}, {0, 1}, {3, 0}, {3, 1}};
  EXPECT_EQ(kept, expected);
}

TEST(Coverage, EmptyIgnoreSelectionLeavesProductsIntact) {
  auto all = CoverageDB::EnumerateCrossProducts({2, 2});
  ASSERT_EQ(all.size(), 4u);
  auto kept = CoverageDB::ExcludeIgnoredCrossProducts(all, {});
  EXPECT_EQ(kept, all);
}

TEST(Coverage, IgnoringAllProductsExcludesEverything) {
  auto all = CoverageDB::EnumerateCrossProducts({2, 2});
  auto kept = CoverageDB::ExcludeIgnoredCrossProducts(all, all);
  EXPECT_TRUE(kept.empty());
}

TEST(Coverage, IgnoredProductExcludedFromOtherCrossBin) {
  std::vector<std::vector<size_t>> user_bin = {{1, 0}, {0, 0}};
  std::vector<std::vector<size_t>> ignored = {{1, 0}, {1, 1}};

  auto effective = CoverageDB::ExcludeIgnoredCrossProducts(user_bin, ignored);
  std::vector<std::vector<size_t>> expected = {{0, 0}};
  EXPECT_EQ(effective, expected);
}

TEST(Coverage, OnlyMatchingProductsAreExcluded) {
  std::vector<std::vector<size_t>> products = {{0, 0}, {0, 1}, {1, 0}};
  std::vector<std::vector<size_t>> ignored = {{1, 0}, {0, 2}, {2, 2}};

  auto kept = CoverageDB::ExcludeIgnoredCrossProducts(products, ignored);
  std::vector<std::vector<size_t>> expected = {{0, 0}, {0, 1}};
  EXPECT_EQ(kept, expected);
}

TEST(Coverage, IgnoredProductNeverRetained) {
  EXPECT_FALSE(CoverageDB::IgnoredCrossProductRetained(true));
  EXPECT_FALSE(CoverageDB::IgnoredCrossProductRetained(false));
}

TEST(CovergroupInstanceSim, IgnoreBinsExcludeTheirProducts) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [1:0] x, y; int n, t;\n"
          "  covergroup cg;\n"
          "    coverpoint x; coverpoint y;\n"
          "    xy: cross x, y { ignore_bins ig = binsof(x) intersect {0}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin void'(c.get_inst_coverage(n, t)); $display(\"n=%0d "
          "t=%0d\", n, t); end\n"
          "endmodule\n",
          f),
      "n=0 t=20\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
