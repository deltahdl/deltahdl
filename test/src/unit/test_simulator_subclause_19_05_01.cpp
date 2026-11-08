#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, ExplicitBinCreation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  CoverBin bin;
  bin.name = "low";
  bin.kind = CoverBinKind::kExplicit;
  bin.values = {0, 1, 2, 3};
  auto* b = CoverageDB::AddBin(cp, bin);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->name, "low");
  EXPECT_EQ(b->values.size(), 4u);
}

TEST(Coverage, SampleHitsExplicitBin) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "val");
  CoverBin bin;
  bin.name = "ones";
  bin.values = {1};
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"val", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);

  db.Sample(g, {{"val", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);

  db.Sample(g, {{"val", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 2u);
}

TEST(Coverage, AutoBinCreation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 7);
  EXPECT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].ranges, (std::vector<CoverValueRange>{{0, 1}}));
  EXPECT_EQ(cp->bins[3].ranges, (std::vector<CoverValueRange>{{6, 7}}));
}

TEST(Coverage, AutoBinSmallRange) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 64;
  CoverageDB::AutoCreateBins(cp, 0, 3);

  EXPECT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].ranges, (std::vector<CoverValueRange>{{0, 0}}));
}

TEST(Coverage, IntegralFixedBinDistribution) {
  std::vector<int64_t> values;
  for (int64_t v = 1; v <= 10; ++v) values.push_back(v);
  values.push_back(1);
  values.push_back(4);
  values.push_back(7);

  auto bins = CoverageDB::DistributeValues(values, 4);
  ASSERT_EQ(bins.size(), 4u);
  EXPECT_EQ(bins[0], (std::vector<int64_t>{1, 2, 3}));
  EXPECT_EQ(bins[1], (std::vector<int64_t>{4, 5, 6}));
  EXPECT_EQ(bins[2], (std::vector<int64_t>{7, 8, 9}));
  EXPECT_EQ(bins[3], (std::vector<int64_t>{10, 1, 4, 7}));
}

TEST(Coverage, IntegralFixedBinMoreBinsThanValues) {
  auto bins = CoverageDB::DistributeValues({1, 4, 7}, 5);
  ASSERT_EQ(bins.size(), 5u);
  EXPECT_EQ(bins[0], (std::vector<int64_t>{1}));
  EXPECT_EQ(bins[1], (std::vector<int64_t>{4}));
  EXPECT_EQ(bins[2], (std::vector<int64_t>{7}));
  EXPECT_TRUE(bins[3].empty());
  EXPECT_TRUE(bins[4].empty());
}

TEST(Coverage, RealFixedBinItemDistribution) {
  std::vector<int64_t> items{0, 1, 2, 3, 4, 5, 6, 7, 8};
  auto bins = CoverageDB::DistributeValues(items, 4);
  ASSERT_EQ(bins.size(), 4u);
  EXPECT_EQ(bins[0], (std::vector<int64_t>{0, 1}));
  EXPECT_EQ(bins[1], (std::vector<int64_t>{2, 3}));
  EXPECT_EQ(bins[2], (std::vector<int64_t>{4, 5}));
  EXPECT_EQ(bins[3], (std::vector<int64_t>{6, 7, 8}));
}

TEST(Coverage, StateBinNaming) {
  EXPECT_EQ(CoverageDB::StateBinName("c", 200), "c[200]");
  EXPECT_EQ(CoverageDB::StateBinName("c", 202), "c[202]");
  EXPECT_EQ(CoverageDB::StateBinName("d", 0), "d[0]");
  EXPECT_EQ(CoverageDB::StateBinName("d", 7), "d[7]");
}

TEST(Coverage, IntegralOpenArrayBins) {
  auto bins = CoverageDB::OpenArrayValueBins("c", {200, 201, 202});
  ASSERT_EQ(bins.size(), 3u);
  EXPECT_EQ(bins[0].name, "c[200]");
  EXPECT_EQ(bins[1].name, "c[201]");
  EXPECT_EQ(bins[2].name, "c[202]");
  EXPECT_EQ(bins[0].values, (std::vector<int64_t>{200}));
}

TEST(Coverage, IntegralOpenArrayDedupesOverlap) {
  std::vector<int64_t> values;
  for (int64_t v = 127; v <= 150; ++v) values.push_back(v);
  for (int64_t v = 148; v <= 191; ++v) values.push_back(v);

  auto bins = CoverageDB::OpenArrayValueBins("b", values);
  ASSERT_EQ(bins.size(), 65u);
  EXPECT_EQ(bins.front().name, "b[127]");
  EXPECT_EQ(bins.back().name, "b[191]");
}

TEST(Coverage, RealRangeDividedIntoIntervals) {
  auto ivs = CoverageDB::RealRangeIntervals(1.0, 4.0, 1.0, false);
  ASSERT_EQ(ivs.size(), 3u);
  EXPECT_NEAR(ivs[0].low, 1.0, 1e-9);
  EXPECT_NEAR(ivs[0].high, 2.0, 1e-9);
  EXPECT_FALSE(ivs[0].high_inclusive);
  EXPECT_NEAR(ivs[1].low, 2.0, 1e-9);
  EXPECT_NEAR(ivs[1].high, 3.0, 1e-9);
  EXPECT_FALSE(ivs[1].high_inclusive);
  EXPECT_NEAR(ivs[2].low, 3.0, 1e-9);
  EXPECT_NEAR(ivs[2].high, 4.0, 1e-9);
  EXPECT_TRUE(ivs[2].high_inclusive);
}

TEST(Coverage, RealRangeIntervalEdgeCases) {
  auto exact = CoverageDB::RealRangeIntervals(1.0, 2.0, 1.0, false);
  ASSERT_EQ(exact.size(), 1u);
  EXPECT_TRUE(exact[0].high_inclusive);

  auto uneven = CoverageDB::RealRangeIntervals(1.0, 2.5, 1.0, false);
  ASSERT_EQ(uneven.size(), 2u);
  EXPECT_NEAR(uneven[1].low, 2.0, 1e-9);
  EXPECT_NEAR(uneven[1].high, 2.5, 1e-9);
  EXPECT_TRUE(uneven[1].high_inclusive);
}

TEST(Coverage, RealDollarRangeIsSingleBin) {
  auto dollar = CoverageDB::RealRangeIntervals(0.75, 100.0, 1.0, true);
  EXPECT_EQ(dollar.size(), 1u);

  auto ordinary = CoverageDB::RealRangeIntervals(0.75, 100.0, 1.0, false);
  EXPECT_GT(ordinary.size(), 1u);
}

TEST(Coverage, RealBinNaming) {
  EXPECT_EQ(CoverageDB::RealIntervalBinName("a2", {1.0, 2.0, false}),
            "a2[1.0:2.0)");
  EXPECT_EQ(CoverageDB::RealIntervalBinName("a2", {2.0, 3.0, true}),
            "a2[2.0:3.0]");
  EXPECT_EQ(CoverageDB::RealIntervalBinName("a2", {8.4, 8.6, true}),
            "a2[8.4:8.6]");
  EXPECT_EQ(CoverageDB::RealValueBinName("a2", 7.5), "a2[7.5]");
}

TEST(Coverage, RealIdenticalIntervalsMerged) {
  std::vector<RealInterval> intervals{
      {2.0, 3.0, false},
      {2.0, 3.0, false},
      {3.0, 4.0, false},
      {3.0, 4.0, true},
  };
  auto merged = CoverageDB::MergeIdenticalIntervals(intervals);
  ASSERT_EQ(merged.size(), 3u);
  EXPECT_FALSE(merged[1].high_inclusive);
  EXPECT_TRUE(merged[2].high_inclusive);
}

TEST(Coverage, RealDefaultBinCannotBeArray) {
  EXPECT_FALSE(CoverageDB::RealDefaultBinMayBeArray());
}

TEST(Coverage, AbsoluteToleranceDefinesRange) {
  auto range = CoverageDB::ToleranceRange(-100.0, 0.1, false);
  EXPECT_NEAR(range.first, -100.1, 1e-9);
  EXPECT_NEAR(range.second, -99.9, 1e-9);
}

TEST(Coverage, RelativeToleranceDefinesRange) {
  auto range = CoverageDB::ToleranceRange(100.0, 1.0, true);
  EXPECT_NEAR(range.first, 99.0, 1e-9);
  EXPECT_NEAR(range.second, 101.0, 1e-9);
}

TEST(Coverage, ToleranceRangeObeysIntervalDivision) {
  auto narrow = CoverageDB::ToleranceRange(-100.0, 0.1, false);
  auto narrow_ivs =
      CoverageDB::RealRangeIntervals(narrow.first, narrow.second, 1.0, false);
  EXPECT_EQ(narrow_ivs.size(), 1u);

  auto wide = CoverageDB::ToleranceRange(100.0, 1.0, true);
  auto wide_ivs =
      CoverageDB::RealRangeIntervals(wide.first, wide.second, 1.0, false);
  EXPECT_EQ(wide_ivs.size(), 2u);
  EXPECT_TRUE(wide_ivs.back().high_inclusive);
}

TEST(Coverage, PerBinIffGuard) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "guarded";
  bin.values = {5};
  bin.has_iff_guard = true;
  bin.iff_guard_value = false;
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 5}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);

  g->coverpoints[0].bins[0].iff_guard_value = true;
  db.Sample(g, {{"v", 5}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

TEST(CovergroupInstanceSim, ArrayAndFixedCountBinsFromDeclaration) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [3:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v {\n"
                       "      bins b[] = {[1:3]}; bins f[2] = {4, 5, 6};\n"
                       "      bins top = {[14:$]}; bins bot = {[$:0]};\n"
                       "    }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 1; c.sample();\n"
                       "    v = 4; c.sample();\n"
                       "    v = 15; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=3 t=7\n");
}

TEST(CovergroupInstanceSim, RangeBinHoldsEveryValueOfItsRange) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  int v; int n, t;\n"
          "  covergroup cg;\n"
          "    coverpoint v { bins big = {[0:100000]}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin v = 99999; c.sample(); void'(c.get_inst_coverage(n, "
          "t)); $display(\"n=%0d t=%0d\", n, t); end\n"
          "endmodule\n",
          f),
      "n=1 t=1\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, BinIffGuardKeepsCountFromIncrementing) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v; bit en;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins lo = {0} iff (en); bins hi = {3}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    en = 0; v = 0; c.sample();\n"
                 "    v = 3; c.sample();\n"
                 "    $display(\"cov=%0.2f\", c.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, RealCoverpointRangeBinCountsRealSample) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  real r; int n, t;\n"
          "  covergroup cg;\n"
          "    coverpoint r { bins a = {[1.0:2.0]}; bins b = {[3.0:4.0]}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n"
          "    r = 1.5; c.sample();\n"
          "    void'(c.get_inst_coverage(n, t));\n"
          "    $display(\"n=%0d t=%0d\", n, t);\n"
          "  end\n"
          "endmodule\n",
          f),
      "n=1 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, TransitionBinIffGuardSuppressesItsCount) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; bit en; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins t = (1 => 2) iff (en); bins u "
                       "= (2 => 3); }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin en = 0; v = 1; c.sample(); v = 2; "
                       "c.sample(); void'(c.get_inst_coverage(n, t)); "
                       "$display(\"n=%0d t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=0 t=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, DefaultBinIffGuardSuppressesItsCount) {
  SimFixture f;
  RunCapture(
      "module top;\n"
      "  bit [3:0] v; bit en;\n"
      "  covergroup cg;\n"
      "    coverpoint v { bins a = {1}; bins other = default iff (en); }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n"
      "    v = 5; en = 0; c.sample();\n"
      "    v = 6; en = 1; c.sample();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  const CoverGroup* group = f.ctx.CoverageData().FindGroup("c");
  ASSERT_NE(group, nullptr);
  const CoverBin& other = group->coverpoints[0].bins.back();
  EXPECT_EQ(other.name, "other");
  EXPECT_EQ(other.hit_count, 1u);
}

TEST(CovergroupInstanceSim, NonPositiveBinCountFromAFormalIsReported) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [3:0] v; real r; int n, t;\n"
                       "  covergroup cg (int k);\n"
                       "    coverpoint v { bins b[k] = {[0:15]}; }\n"
                       "  endgroup\n"
                       "  covergroup rg (int k);\n"
                       "    coverpoint r { bins b[k] = {[0.0:4.0]}; }\n"
                       "  endgroup\n"
                       "  cg c0 = new(0);\n"
                       "  cg c1 = new(-2);\n"
                       "  cg c2 = new(4);\n"
                       "  rg r0 = new(0);\n"
                       "  initial begin void'(c2.get_inst_coverage(n, t)); "
                       "$display(\"t=%0d\", t); end\n"
                       "endmodule\n",
                       f),
            "t=4\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "bins 'b' asks for 0 bins", 4,
                            "19.5.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "bins 'b' asks for -2 bins",
                            4, "19.5.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "bins 'b' asks for 0 bins", 7,
                            "19.5.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace
