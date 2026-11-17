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

std::string CrossBinHits(const std::string& body, const std::string& samples) {
  SimFixture f;
  RunCapture(
      "module top;\n"
      "  bit [2:0] x; bit [1:0] y; bit en;\n"
      "  covergroup cg;\n"
      "    cx: coverpoint x { bins b0 = {0}; bins b1 = {1}; bins b23 = "
      "{[2:3]};\n"
      "      bins b45 = {[4:5]}; bins b67 = {[6:7]}; }\n"
      "    cy: coverpoint y { bins c0 = {0}; bins c1 = {1}; bins c2 = {2}; }\n"
      "    xy: cross cx, cy {\n" +
          body +
          "    }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n" +
          samples +
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  const CoverGroup* group = f.ctx.CoverageData().FindGroup("c");
  if (group == nullptr || group->crosses.empty()) return "no cross";
  std::string hits;
  for (const CrossBin& bin : group->crosses[0].bins) {
    hits += bin.name + "=" + std::to_string(bin.bin_tuples.size()) + ":" +
            std::to_string(bin.hit_count) + " ";
  }
  return hits;
}

TEST(CovergroupInstanceSim, BinsofOneBinSelectsOnlyThatBinsProducts) {
  EXPECT_EQ(CrossBinHits("      option.cross_retain_auto_bins = 0;\n"
                         "      bins one = binsof(cx.b23);\n",
                         "    x = 3; y = 2; c.sample();\n"
                         "    x = 4; y = 2; c.sample();\n"),
            "one=3:1 ");
}

TEST(CovergroupInstanceSim, NegatedBinsofSelectsBinsHoldingNoneOfTheValues) {
  EXPECT_EQ(CrossBinHits("      option.cross_retain_auto_bins = 0;\n"
                         "      bins neg = ! binsof(cx) intersect {1, 5};\n",
                         "    x = 4; y = 0; c.sample();\n"
                         "    x = 6; y = 0; c.sample();\n"),
            "neg=9:1 ");
}

TEST(CovergroupInstanceSim, EveryIntersectRangeFormSelectsOverlappingBins) {
  EXPECT_EQ(CrossBinHits("      option.cross_retain_auto_bins = 0;\n"
                         "      bins r = binsof(cx) intersect {[1:2]};\n"
                         "      bins lo = binsof(cx) intersect {[$:1]};\n"
                         "      bins hi = binsof(cx) intersect {[5:$]};\n"
                         "      bins pm = binsof(cx) intersect {[3 +/- 1]};\n"
                         "      bins pc = binsof(cx) intersect {[6 +%- 20]};\n",
                         "    x = 2; y = 1; c.sample();\n"),
            "r=6:1 lo=6:0 hi=6:0 pm=6:1 pc=6:0 ");
}

TEST(CovergroupInstanceSim, AndLeavesOutAProductOnlyOneOperandSelects) {
  EXPECT_EQ(CrossBinHits("      option.cross_retain_auto_bins = 0;\n"
                         "      bins a = binsof(cx) intersect {0} &&\n"
                         "               binsof(cy) intersect {1};\n"
                         "      bins o = binsof(cx) intersect {0} ||\n"
                         "               binsof(cy) intersect {1};\n"
                         "      bins p = binsof(cx) intersect {0} &&\n"
                         "               (binsof(cy) intersect {1} ||\n"
                         "                binsof(cy) intersect {2});\n",
                         "    x = 0; y = 0; c.sample();\n"
                         "    x = 4; y = 1; c.sample();\n"
                         "    x = 4; y = 2; c.sample();\n"
                         "    x = 0; y = 2; c.sample();\n"),
            "a=1:0 o=7:3 p=2:1 ");
}

TEST(CovergroupInstanceSim, ACrossBinCountsOncePerSampleMatchingAnyProduct) {
  EXPECT_EQ(
      CrossBinHits("      option.cross_retain_auto_bins = 0;\n"
                   "      bins two = binsof(cx.b0) && binsof(cy) intersect "
                   "{[0:1]};\n",
                   "    x = 0; y = 0; c.sample();\n"
                   "    x = 0; y = 1; c.sample();\n"
                   "    x = 0; y = 2; c.sample();\n"
                   "    x = 0; y = 1; c.sample();\n"),
      "two=2:3 ");
}

TEST(CovergroupInstanceSim, AFalseBinIffGuardLeavesOnlyThatBinUncounted) {
  EXPECT_EQ(CrossBinHits("      option.cross_retain_auto_bins = 0;\n"
                         "      bins g = binsof(cx.b1) iff (en);\n"
                         "      bins u = binsof(cy.c2);\n",
                         "    en = 0; x = 1; y = 2; c.sample();\n"
                         "    en = 1; x = 1; y = 0; c.sample();\n"),
            "g=3:1 u=5:1 ");
}

TEST(CovergroupInstanceSim, ABinsofOfACrossedVariableNamesItsCoverpoint) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] a; bit b; int n, t;\n"
                       "  covergroup cg;\n"
                       "    ab: cross a, b {\n"
                       "      option.cross_retain_auto_bins = 0;\n"
                       "      bins s = binsof(a) intersect {2};\n"
                       "    }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    a = 2; b = 1; c.sample();\n"
                       "    void'(c.ab.get_inst_coverage(n, t));\n"
                       "    $display(\"%0d %0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, RetainAutoBinsOffInACrossBodyLeavesOnlyUserBins) {
  EXPECT_EQ(CrossBinHits("      option.cross_retain_auto_bins = 0;\n"
                         "      bins s = binsof(cx.b0);\n",
                         "    x = 7; y = 1; c.sample();\n"),
            "s=3:0 ");
}

TEST(CovergroupInstanceSim, AutomaticCrossBinsStayForProductsNoUserBinSelects) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] a, b; int n, t;\n"
                 "  covergroup cg;\n"
                 "    option.cross_retain_auto_bins = 0;\n"
                 "    ca: coverpoint a { bins a0 = {0}; bins a1 = {1}; }\n"
                 "    cb: coverpoint b { bins b0 = {0}; bins b1 = {1}; }\n"
                 "    xu: cross ca, cb { bins s = binsof(ca.a0); }\n"
                 "    xn: cross ca, cb;\n"
                 "    xk: cross ca, cb {\n"
                 "      option.cross_retain_auto_bins = 1;\n"
                 "      bins s = binsof(ca.a0);\n"
                 "    }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    a = 1; b = 1; c.sample();\n"
                 "    void'(c.xu.get_inst_coverage(n, t)); $write(\"%0d %0d "
                 "\", n, t);\n"
                 "    void'(c.xn.get_inst_coverage(n, t)); $write(\"%0d %0d "
                 "\", n, t);\n"
                 "    void'(c.xk.get_inst_coverage(n, t)); $display(\"%0d "
                 "%0d\", n, t);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "0 1 1 4 1 3\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
