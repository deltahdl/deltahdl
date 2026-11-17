#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
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

std::string RunSource(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(TypeCoverageSim, UnmergedTypeAveragesInstancesByOptionWeight) {
  EXPECT_EQ(
      RunSource("module t;\n"
                "  covergroup cg(int w) with function sample(bit [1:0] v);\n"
                "    option.weight = w;\n"
                "    coverpoint v { bins b[] = {[0:3]}; }\n"
                "  endgroup\n"
                "  cg c1 = new(1);\n"
                "  cg c2 = new(3);\n"
                "  initial begin\n"
                "    c1.sample(0); c1.sample(1);\n"
                "    for (int i = 0; i < 4; i++) c2.sample(i);\n"
                "    $display(\"%0.2f\", cg::get_coverage());\n"
                "  end\n"
                "endmodule\n"),
      "87.50\n");
}

TEST(TypeCoverageSim, UnmergedTypeIgnoresTheItemsTypeWeights) {
  EXPECT_EQ(
      RunSource(
          "module t;\n"
          "  covergroup cg with function sample(bit a, bit b);\n"
          "    pa: coverpoint a { type_option.weight = 3; bins one = {1}; }\n"
          "    pb: coverpoint b { type_option.weight = 1; bins one = {1}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n"
          "    c.sample(1, 0);\n"
          "    $display(\"%0.2f\", cg::get_coverage());\n"
          "  end\n"
          "endmodule\n"),
      "50.00\n");
}

TEST(TypeCoverageSim, DISABLED_UnmergedTypeCountsAgreeWithTheWeightedAverage) {
  EXPECT_EQ(
      RunSource("module t;\n"
                "  int n, m;\n"
                "  real r;\n"
                "  covergroup cg(int w) with function sample(bit [1:0] v);\n"
                "    option.weight = w;\n"
                "    coverpoint v { bins b[] = {[0:3]}; }\n"
                "  endgroup\n"
                "  cg c1 = new(1);\n"
                "  cg c2 = new(3);\n"
                "  initial begin\n"
                "    c1.sample(0); c1.sample(1);\n"
                "    for (int i = 0; i < 4; i++) c2.sample(i);\n"
                "    r = cg::get_coverage(n, m);\n"
                "    $display(\"%0.2f %0.2f\", r, 100.0 * n / m);\n"
                "  end\n"
                "endmodule\n"),
      "87.50 87.50\n");
}

TEST(TypeCoverageSim, ItemTypeCoverageAveragesInstancesByTheItemsWeight) {
  EXPECT_EQ(
      RunSource(
          "module t;\n"
          "  covergroup cg(int w) with function sample(bit [1:0] a, bit b);\n"
          "    pa: coverpoint a { option.weight = w; bins x[] = {[0:3]}; }\n"
          "    pb: coverpoint b { bins y[] = {0, 1}; }\n"
          "    x: cross pa, pb { option.weight = w; }\n"
          "  endgroup\n"
          "  cg c1 = new(1);\n"
          "  cg c2 = new(3);\n"
          "  initial begin\n"
          "    c1.sample(0, 0); c1.sample(1, 0);\n"
          "    for (int i = 0; i < 4; i++) c2.sample(i, 0);\n"
          "    $display(\"%0.2f %0.2f\", cg::pa::get_coverage(),\n"
          "      cg::x::get_coverage());\n"
          "  end\n"
          "endmodule\n"),
      "87.50 43.75\n");
}

const char kStandardsMergedExample[] =
    "module t;\n"
    "  bit [1:0] a;\n"
    "  int n, m;\n"
    "  covergroup gt(int l, h);\n"
    "    option.get_inst_coverage = 1;\n"
    "    type_option.merge_instances = 1;\n"
    "    coverpoint a { bins b[] = {[l:h]}; }\n"
    "  endgroup\n"
    "  gt gv1 = new(0, 1);\n"
    "  gt gv2 = new(1, 2);\n"
    "  initial begin\n"
    "    a = 0; gv1.sample();\n"
    "    a = 1; gv1.sample(); gv2.sample();\n";

TEST(TypeCoverageSim, TheStandardsMergedExampleUnionsOverlappingValueBins) {
  EXPECT_EQ(
      RunSource(std::string(kStandardsMergedExample) +
                "    $display(\"%0.2f %0.2f %0.2f\", gt::get_coverage(),\n"
                "      gv1.get_inst_coverage(), gv2.get_inst_coverage());\n"
                "  end\n"
                "endmodule\n"),
      "66.67 100.00 50.00\n");
}

TEST(TypeCoverageSim, DISABLED_AMergedTypesCountsAreTheUnionsCounts) {
  EXPECT_EQ(RunSource(std::string(kStandardsMergedExample) +
                      "    void'(gt::get_coverage(n, m));\n"
                      "    $display(\"%0d %0d\", n, m);\n"
                      "  end\n"
                      "endmodule\n"),
            "2 3\n");
}

std::string MergedCoverage(const std::string& declarations,
                           const std::string& samples, const char* item) {
  return RunSource(std::string("module t;\n") + declarations +
                   "  initial begin\n" + samples + "    $display(\"%0.2f\", " +
                   item +
                   "::get_coverage());\n"
                   "  end\n"
                   "endmodule\n");
}

TEST(TypeCoverageSim, MergedFixedCountBinsOverlapByIndex) {
  EXPECT_EQ(MergedCoverage(
                "  covergroup g(int l, h) with function sample(bit [2:0] v);\n"
                "    type_option.merge_instances = 1;\n"
                "    coverpoint v { bins b[2] = {[l:h]}; }\n"
                "  endgroup\n"
                "  g g1 = new(0, 3);\n"
                "  g g2 = new(4, 7);\n",
                "    g1.sample(0); g2.sample(6);\n", "g"),
            "100.00\n");
}

TEST(TypeCoverageSim, MergedScalarBinIsSharedByEveryInstance) {
  EXPECT_EQ(MergedCoverage(
                "  covergroup g(int l, h) with function sample(bit [1:0] v);\n"
                "    type_option.merge_instances = 1;\n"
                "    coverpoint v { bins s = {[l:h]}; }\n"
                "  endgroup\n"
                "  g g1 = new(0, 1);\n"
                "  g g2 = new(2, 3);\n",
                "    g1.sample(0);\n", "g"),
            "100.00\n");
}

TEST(TypeCoverageSim, MergedAutomaticBinsKeepTheirNamesUnderIgnoredValues) {
  EXPECT_EQ(MergedCoverage(
                "  covergroup ga(int abm) with function sample(bit [7:0] a);\n"
                "    type_option.merge_instances = 1;\n"
                "    option.auto_bin_max = abm;\n"
                "    coverpoint a { ignore_bins i = {3}; }\n"
                "  endgroup\n"
                "  ga gv1 = new(64);\n"
                "  ga gv2 = new(32);\n",
                "    gv1.sample(0); gv2.sample(0);\n", "ga"),
            "2.08\n");
}

TEST(TypeCoverageSim, MergedAutomaticBinsKeepTheirNamesUnderIllegalValues) {
  EXPECT_EQ(MergedCoverage(
                "  covergroup ga(int abm) with function sample(bit [7:0] a);\n"
                "    type_option.merge_instances = 1;\n"
                "    option.auto_bin_max = abm;\n"
                "    coverpoint a { illegal_bins i = {3}; }\n"
                "  endgroup\n"
                "  ga gv1 = new(64);\n"
                "  ga gv2 = new(64);\n",
                "    gv1.sample(0);\n", "ga"),
            "1.56\n");
}

TEST(TypeCoverageSim, MergedTransitionBinsOverlapByTransition) {
  EXPECT_EQ(MergedCoverage(
                "  covergroup g(int l, h) with function sample(bit [1:0] v);\n"
                "    type_option.merge_instances = 1;\n"
                "    coverpoint v { bins t[] = (l, h => 3); }\n"
                "  endgroup\n"
                "  g g1 = new(0, 1);\n"
                "  g g2 = new(1, 2);\n",
                "    g1.sample(0); g1.sample(3);\n"
                "    g2.sample(1); g2.sample(3);\n",
                "g"),
            "66.67\n");
}

TEST(TypeCoverageSim, MergedAutomaticCrossBinsOverlapByProductName) {
  EXPECT_EQ(
      MergedCoverage(
          "  covergroup g(int l, h) with function sample(bit [1:0] a, bit b);\n"
          "    type_option.merge_instances = 1;\n"
          "    pa: coverpoint a { bins x[] = {[l:h]}; }\n"
          "    pb: coverpoint b { bins y[] = {0, 1}; }\n"
          "    ab: cross pa, pb;\n"
          "  endgroup\n"
          "  g g1 = new(0, 1);\n"
          "  g g2 = new(1, 2);\n",
          "    g1.sample(1, 0); g2.sample(1, 0);\n", "g::ab"),
      "16.67\n");
}

}  // namespace
