#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_coverage.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, CrossCoverageComputation) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);

  db.Sample(g, {{"a", 0}, {"b", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&g->crosses[0]), 50.0);
}

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

TEST(Coverage, IntersectSelectsBinsByValueOverlap) {
  CoverPoint i = MakeTwoBinPoint("i");
  auto bins = CoverageDB::BinsofYield(&i);

  auto included = CoverageDB::SelectBinsByIntersect(bins, {0}, false);
  EXPECT_EQ(included, (std::vector<size_t>{0}));

  auto excluded = CoverageDB::SelectBinsByIntersect(bins, {0}, true);
  EXPECT_EQ(excluded, (std::vector<size_t>{1}));
}

TEST(Coverage, UserCrossBinAndRetainedAutoBins) {
  CoverPoint i = MakeTwoBinPoint("i");
  std::vector<size_t> counts = {2, 2};

  auto i_bins = CoverageDB::BinsofYield(&i);
  auto i_sel = CoverageDB::SelectBinsByIntersect(i_bins, {0}, false);
  auto user = CoverageDB::SelectProductsByPointBins(counts, 0, i_sel);

  EXPECT_EQ(user, (std::vector<std::vector<size_t>>{{0, 0}, {0, 1}}));

  auto retained = CoverageDB::RetainedAutoCrossProducts(counts, user, true);
  EXPECT_EQ(retained, (std::vector<std::vector<size_t>>{{1, 0}, {1, 1}}));

  auto none = CoverageDB::RetainedAutoCrossProducts(counts, user, false);
  EXPECT_TRUE(none.empty());
}

TEST(Coverage, SelectionsCombineWithAndOr) {
  std::vector<size_t> counts = {2, 2};
  auto sel_i0 = CoverageDB::SelectProductsByPointBins(counts, 0, {0});
  auto sel_j1 = CoverageDB::SelectProductsByPointBins(counts, 1, {1});

  auto both = CoverageDB::AndCrossSelections(sel_i0, sel_j1);
  EXPECT_EQ(both, (std::vector<std::vector<size_t>>{{0, 1}}));

  auto either = CoverageDB::OrCrossSelections(sel_i0, sel_j1);
  EXPECT_EQ(either, (std::vector<std::vector<size_t>>{{0, 0}, {0, 1}, {1, 1}}));
}

TEST(Coverage, CrossBinCountsAnyMatchingProduct) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "i");
  CoverageDB::AddCoverPoint(g, "j");

  CrossCover cross;
  cross.name = "iXj";
  cross.coverpoint_names = {"i", "j"};
  CrossBin i_zero;
  i_zero.name = "i_zero";
  i_zero.value_sets = {{0}, {0, 1}};
  cross.bins.push_back(i_zero);
  CoverageDB::AddCross(g, cross);

  CrossBin* bin = &g->crosses[0].bins[0];
  db.Sample(g, {{"i", 0}, {"j", 0}});
  EXPECT_EQ(bin->hit_count, 1u);
  db.Sample(g, {{"i", 0}, {"j", 1}});
  EXPECT_EQ(bin->hit_count, 2u);
  db.Sample(g, {{"i", 1}, {"j", 0}});
  EXPECT_EQ(bin->hit_count, 2u);
}

TEST(Coverage, BinsofYieldHandlesEmptyAndOutOfRange) {
  EXPECT_TRUE(CoverageDB::BinsofYield(nullptr).empty());

  CoverPoint i = MakeTwoBinPoint("i");
  EXPECT_TRUE(CoverageDB::BinsofYield(&i, 2).empty());

  CoverPoint empty;
  empty.name = "empty";
  EXPECT_TRUE(CoverageDB::BinsofYield(&empty).empty());
}

TEST(Coverage, IntersectMatchesOnAnyValueOverlap) {
  std::vector<std::vector<int64_t>> bins = {{2, 3, 4}, {6, 7}};

  auto included = CoverageDB::SelectBinsByIntersect(bins, {4, 5}, false);
  EXPECT_EQ(included, (std::vector<size_t>{0}));

  auto excluded = CoverageDB::SelectBinsByIntersect(bins, {4, 5}, true);
  EXPECT_EQ(excluded, (std::vector<size_t>{1}));

  EXPECT_TRUE(CoverageDB::SelectBinsByIntersect(bins, {}, false).empty());
  EXPECT_EQ(CoverageDB::SelectBinsByIntersect(bins, {}, true),
            (std::vector<size_t>{0, 1}));
}

TEST(Coverage, NoCrossProductsWhenACoverpointHasNoBins) {
  EXPECT_TRUE(CoverageDB::EnumerateCrossProducts({2, 0}).empty());
}

TEST(Coverage, EmptyAndDisjointSelectionsDenoteNoProducts) {
  std::vector<size_t> counts = {2, 2};

  EXPECT_TRUE(CoverageDB::SelectProductsByPointBins(counts, 0, {}).empty());

  auto i0 = CoverageDB::SelectProductsByPointBins(counts, 0, {0});
  auto i1 = CoverageDB::SelectProductsByPointBins(counts, 0, {1});
  EXPECT_TRUE(CoverageDB::AndCrossSelections(i0, i1).empty());
}

TEST(Coverage, NoAutoBinsRetainedWhenUserBinsCoverAll) {
  std::vector<size_t> counts = {2, 2};
  auto all = CoverageDB::EnumerateCrossProducts(counts);
  ASSERT_EQ(all.size(), 4u);

  auto retained = CoverageDB::RetainedAutoCrossProducts(counts, all, true);
  EXPECT_TRUE(retained.empty());
}

TEST(CovergroupInstanceSim, UserCrossBinReplacesTheProductsItSelects) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit x, y; int n, t;\n"
          "  covergroup cg;\n"
          "    cx: coverpoint x { bins a = {0}; bins b = {1}; }\n"
          "    cy: coverpoint y { bins a = {0}; bins b = {1}; }\n"
          "    xy: cross cx, cy { bins sel = binsof(cx) intersect {0}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin x = 1; y = 1; c.sample(); "
          "void'(c.get_inst_coverage(n, t)); $display(\"n=%0d t=%0d\", n, t); "
          "end\n"
          "endmodule\n",
          f),
      "n=3 t=7\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
