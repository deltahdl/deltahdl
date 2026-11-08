#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
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

TEST(Coverage, IllegalBinsExcludesSelectedCrossProducts) {
  CoverPoint y;
  y.name = "y";
  y.bins = {MakeValueBin("y0", {0}), MakeValueBin("y1", {7}),
            MakeValueBin("y2", {9})};

  std::vector<size_t> per_point_bin_counts = {2, 3};
  auto all = CoverageDB::EnumerateCrossProducts(per_point_bin_counts);
  ASSERT_EQ(all.size(), 6u);

  auto y_bins = CoverageDB::BinsofYield(&y);
  auto selected_y = CoverageDB::SelectBinsByIntersect(y_bins, {7}, false);
  EXPECT_EQ(selected_y, (std::vector<size_t>{1}));

  auto illegal = CoverageDB::SelectProductsByPointBins(per_point_bin_counts, 1,
                                                       selected_y);
  EXPECT_EQ(illegal.size(), 2u);

  auto kept = CoverageDB::ExcludeIllegalCrossProducts(all, illegal);
  std::vector<std::vector<size_t>> expected = {{0, 0}, {0, 2}, {1, 0}, {1, 2}};
  EXPECT_EQ(kept, expected);
}

TEST(Coverage, SampledIllegalCrossProductRaisesError) {
  std::vector<std::vector<size_t>> illegal = {{1, 0}, {1, 1}};
  std::vector<std::vector<size_t>> ignored = {};

  EXPECT_EQ(CoverageDB::ClassifyCrossSample({1, 0}, illegal, ignored, false),
            CrossSampleOutcome::kIllegalError);
  EXPECT_EQ(CoverageDB::ClassifyCrossSample({0, 0}, illegal, ignored, false),
            CrossSampleOutcome::kCounted);
}

TEST(Coverage, IllegalTakesPrecedenceOverIgnore) {
  std::vector<std::vector<size_t>> illegal = {{1, 0}};
  std::vector<std::vector<size_t>> ignored = {{1, 0}};

  EXPECT_EQ(CoverageDB::ClassifyCrossSample({1, 0}, illegal, ignored, false),
            CrossSampleOutcome::kIllegalError);
}

TEST(Coverage, IllegalTakesPrecedenceOverOtherCrossBin) {
  std::vector<std::vector<size_t>> illegal = {{0, 1}};
  std::vector<std::vector<size_t>> ignored = {};

  EXPECT_EQ(CoverageDB::ClassifyCrossSample({0, 1}, illegal, ignored, true),
            CrossSampleOutcome::kIllegalError);
}

TEST(Coverage, IgnoredNonIllegalProductIsNotAnError) {
  std::vector<std::vector<size_t>> illegal = {{1, 0}};
  std::vector<std::vector<size_t>> ignored = {{0, 1}};

  EXPECT_EQ(CoverageDB::ClassifyCrossSample({0, 1}, illegal, ignored, false),
            CrossSampleOutcome::kIgnored);
}

TEST(Coverage, OnlyMatchingIllegalProductsAreExcluded) {
  std::vector<std::vector<size_t>> products = {{0, 0}, {0, 1}, {1, 0}};
  std::vector<std::vector<size_t>> illegal = {{1, 0}, {0, 2}, {2, 2}};

  auto kept = CoverageDB::ExcludeIllegalCrossProducts(products, illegal);
  std::vector<std::vector<size_t>> expected = {{0, 0}, {0, 1}};
  EXPECT_EQ(kept, expected);

  EXPECT_EQ(CoverageDB::ExcludeIllegalCrossProducts(products, {}), products);
}

TEST(Coverage, IllegalBinsCanExcludeEveryCrossProduct) {
  auto all = CoverageDB::EnumerateCrossProducts({2, 2});
  ASSERT_EQ(all.size(), 4u);
  auto kept = CoverageDB::ExcludeIllegalCrossProducts(all, all);
  EXPECT_TRUE(kept.empty());
}

TEST(Coverage, IllegalPrecedenceHoldsWhenAlsoIgnoredAndInOtherCrossBin) {
  std::vector<std::vector<size_t>> illegal = {{1, 1}};
  std::vector<std::vector<size_t>> ignored = {{1, 1}};

  EXPECT_EQ(CoverageDB::ClassifyCrossSample({1, 1}, illegal, ignored, true),
            CrossSampleOutcome::kIllegalError);
}

TEST(CovergroupInstanceSim, IllegalCrossProductIsRunTimeError) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] x, y;\n"
                       "  covergroup zz (int bad);\n"
                       "    coverpoint x; coverpoint y; cross x, y;\n"
                       "    xy: cross x, y { illegal_bins illegal = binsof(y) "
                       "intersect {bad}; }\n"
                       "  endgroup\n"
                       "  zz c = new(3);\n"
                       "  initial begin\n"
                       "    x = 0; y = 1; c.sample();\n"
                       "    y = 3; c.sample();\n"
                       "    $display(\"done\");\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "done\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sampled values of cross 'xy' fall in its illegal "
                            "bins 'illegal'",
                            10, "19.6.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CovergroupInstanceSim, IllegalSelectionJoinedByAndIsRunTimeError) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [1:0] x, y;\n"
          "  covergroup cg;\n"
          "    coverpoint x; coverpoint y;\n"
          "    xy: cross x, y { illegal_bins bad = binsof(x) intersect {0} && "
          "binsof(y) intersect {1}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin x = 0; y = 1; c.sample(); $display(\"done\"); end\n"
          "endmodule\n",
          f),
      "done\n");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "sampled values of cross 'xy' fall in its illegal bins 'bad'", 8,
      "19.6.3"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
