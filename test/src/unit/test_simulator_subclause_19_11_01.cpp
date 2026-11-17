#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_coverage_point_setup.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(PointCoverage, UserDefinedBinsCoveredOverDefined) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = AddTwoValueBinPoint(g);

  db.Sample(g, {{"x", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 50.0);
}

TEST(PointCoverage, AutoBinDenominatorIsAutoBinCount) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 3);

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetPointCoverage(cp, covered, total);
  EXPECT_EQ(static_cast<uint64_t>(total), CoverageDB::AutoBinCount(2, 4));

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 50.0);
}

TEST(PointCoverage, EmptiedBinExcludedFromBothNumeratorAndDenominator) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 3);

  cp->bins[0].ranges.clear();

  db.Sample(g, {{"x", 1}});
  db.Sample(g, {{"x", 2}});
  db.Sample(g, {{"x", 3}});

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetPointCoverage(cp, covered, total);
  EXPECT_EQ(covered, 3);
  EXPECT_EQ(total, 3);
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(PointCoverage, DenominatorZeroDetection) {
  CoverPoint empty_cp;
  CoverBin no_value;
  no_value.name = "b0";
  empty_cp.bins.push_back(no_value);
  EXPECT_TRUE(CoverageDB::PointCoverageDenominatorZero(&empty_cp));

  CoverPoint valued_cp;
  CoverBin valued;
  valued.name = "b0";
  valued.values = {0};
  valued_cp.bins.push_back(valued);
  EXPECT_FALSE(CoverageDB::PointCoverageDenominatorZero(&valued_cp));
}

TEST(PointCoverage, ZeroDenominatorNonzeroWeightReturnsZero) {
  CoverPoint cp;
  cp.weight = 1;
  CoverBin no_value;
  no_value.name = "b0";
  cp.bins.push_back(no_value);

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(&cp), 0.0);
}

TEST(PointCoverage, ZeroDenominatorZeroWeightReturns100) {
  CoverPoint cp;
  cp.weight = 0;
  CoverBin no_value;
  no_value.name = "b0";
  cp.bins.push_back(no_value);

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(&cp), 100.0);
}

TEST(PointCoverage, ZeroDenominatorCoverpointDroppedFromCovergroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* keep = CoverageDB::AddCoverPoint(g, "keep");
  CoverBin kb;
  kb.name = "b0";
  kb.values = {0};
  CoverageDB::AddBin(keep, kb);

  auto* empty = CoverageDB::AddCoverPoint(g, "empty");
  empty->weight = 1;
  CoverBin no_value;
  no_value.name = "b0";
  CoverageDB::AddBin(empty, no_value);

  db.Sample(g, {{"keep", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 100.0);
}

TEST(PointCoverage, ZeroDenominatorTwoArgReportsZeroCounts) {
  CoverPoint cp;
  CoverBin no_value;
  no_value.name = "b0";
  cp.bins.push_back(no_value);

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetPointCoverage(&cp, covered, total);
  EXPECT_EQ(covered, 0);
  EXPECT_EQ(total, 0);
}

TEST(PointCoverage, CumulativeAtLeastIsMaxOverInstances) {
  EXPECT_EQ(CoverageDB::CumulativeAtLeast({1, 3, 2}), 3u);
  EXPECT_EQ(CoverageDB::CumulativeAtLeast({2, 2}), 2u);
  EXPECT_EQ(CoverageDB::CumulativeAtLeast({}), 1u);
}

TEST(PointCoverage, BinCoveredOnlyAtCumulativeAtLeast) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin bin;
  bin.name = "b0";
  bin.values = {0};
  bin.at_least = CoverageDB::CumulativeAtLeast({1, 2, 3});
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 0.0);

  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(PointCoverage, TransitionBinParticipatesInCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin trans;
  trans.name = "t";
  trans.kind = CoverBinKind::kTransition;
  trans.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, trans);

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetPointCoverage(cp, covered, total);
  EXPECT_EQ(covered, 0);
  EXPECT_EQ(total, 1);
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 0.0);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(PointCoverage, CoverpointWithOnlyExcludedBinsHasZeroDenominator) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin illegal;
  illegal.name = "bad";
  illegal.kind = CoverBinKind::kIllegal;
  illegal.values = {9};
  CoverageDB::AddBin(cp, illegal);

  CoverBin ignore;
  ignore.name = "skip";
  ignore.kind = CoverBinKind::kIgnore;
  ignore.values = {8};
  CoverageDB::AddBin(cp, ignore);

  CoverBin def;
  def.name = "rest";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(cp, def);

  EXPECT_TRUE(CoverageDB::PointCoverageDenominatorZero(cp));
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 0.0);
}

TEST(PointCoverage, UncoveredBinsReportZeroRegardlessOfWeight) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->weight = 0;
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(cp, b0);
  CoverBin b1;
  b1.name = "b1";
  b1.values = {1};
  CoverageDB::AddBin(cp, b1);

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 0.0);
}

std::string RunSource(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(PointCoverageSim, ATransitionBinIsDefinedBeforeItsHitAndCoveredAfter) {
  EXPECT_EQ(
      RunSource("module t;\n"
                "  bit [1:0] v;\n"
                "  int n, m;\n"
                "  covergroup cg;\n"
                "    coverpoint v { bins a = {2}; bins tr = (0 => 1); }\n"
                "  endgroup\n"
                "  cg c = new;\n"
                "  initial begin\n"
                "    void'(c.get_inst_coverage(n, m));\n"
                "    $display(\"%0d %0d\", n, m);\n"
                "    v = 0; c.sample();\n"
                "    v = 1; c.sample();\n"
                "    void'(c.get_inst_coverage(n, m));\n"
                "    $display(\"%0.2f %0.2f %0d %0d\", c.get_inst_coverage(),\n"
                "      c.get_coverage(), n, m);\n"
                "  end\n"
                "endmodule\n"),
      "0 2\n"
      "50.00 50.00 1 2\n");
}

const char kFullyIgnoredPoint[] =
    "module t;\n"
    "  bit a;\n"
    "  bit [1:0] b;\n"
    "  int n, m;\n"
    "  covergroup cg(int w);\n"
    "    cp: coverpoint a { option.weight = w; ignore_bins i = {0, 1}; }\n"
    "    cq: coverpoint b { bins y[] = {[0:3]}; }\n"
    "  endgroup\n";

TEST(PointCoverageSim, AFullyIgnoredCoverpointOfNonzeroWeightReadsZero) {
  EXPECT_EQ(
      RunSource(
          std::string(kFullyIgnoredPoint) +
          "  cg c = new(1);\n"
          "  initial begin\n"
          "    a = 1; b = 1; c.sample();\n"
          "    void'(c.cp.get_inst_coverage(n, m));\n"
          "    $display(\"%0.2f %0.2f %0d %0d\", c.cp.get_inst_coverage(),\n"
          "      cg::cp::get_coverage(), n, m);\n"
          "  end\n"
          "endmodule\n"),
      "0.00 0.00 0 0\n");
}

TEST(PointCoverageSim, AFullyIgnoredCoverpointOfZeroWeightReadsOneHundred) {
  EXPECT_EQ(RunSource(std::string(kFullyIgnoredPoint) +
                      "  cg c = new(0);\n"
                      "  initial begin\n"
                      "    a = 1; b = 1; c.sample();\n"
                      "    $display(\"%0.2f\", c.cp.get_inst_coverage());\n"
                      "  end\n"
                      "endmodule\n"),
            "100.00\n");
}

TEST(PointCoverageSim, AnAutomaticBinEmptiedByIgnoreBinsLeavesBothCounts) {
  EXPECT_EQ(
      RunSource(
          "module t;\n"
          "  bit [2:0] b;\n"
          "  int n, m;\n"
          "  covergroup ct;\n"
          "    coverpoint b {\n"
          "      option.auto_bin_max = 4;\n"
          "      ignore_bins ig = {[0:1], [5:6]};\n"
          "    }\n"
          "  endgroup\n"
          "  ct c = new;\n"
          "  initial begin\n"
          "    b = 0; c.sample();\n"
          "    b = 2; c.sample();\n"
          "    void'(c.get_inst_coverage(n, m));\n"
          "    $display(\"%0.2f %0d %0d\", c.get_inst_coverage(), n, m);\n"
          "  end\n"
          "endmodule\n"),
      "33.33 1 3\n");
}

TEST(PointCoverageSim, AMergedBinIsCoveredOnlyAtTheLargestAtLeast) {
  EXPECT_EQ(RunSource("module t;\n"
                      "  bit a;\n"
                      "  covergroup cg(int al) with function sample(bit v);\n"
                      "    type_option.merge_instances = 1;\n"
                      "    option.at_least = al;\n"
                      "    coverpoint v { bins b[] = {0, 1}; }\n"
                      "  endgroup\n"
                      "  cg c1 = new(1);\n"
                      "  cg c2 = new(3);\n"
                      "  initial begin\n"
                      "    c1.sample(0); c1.sample(0); c2.sample(0);\n"
                      "    c1.sample(1); c1.sample(1);\n"
                      "    $display(\"%0.2f\", cg::get_coverage());\n"
                      "  end\n"
                      "endmodule\n"),
            "50.00\n");
}

TEST(PointCoverageSim, AutomaticBinsNumberTheLesserOfAutoBinMaxAndTheValues) {
  EXPECT_EQ(
      RunSource(
          "module t;\n"
          "  bit [2:0] a;\n"
          "  bit [1:0] b;\n"
          "  int n, m;\n"
          "  covergroup cg(int abm);\n"
          "    p4: coverpoint a { option.auto_bin_max = 4; }\n"
          "    pw: coverpoint b { option.auto_bin_max = 64; }\n"
          "    pa: coverpoint a { option.auto_bin_max = abm; }\n"
          "  endgroup\n"
          "  covergroup cd;\n"
          "    option.auto_bin_max = 2;\n"
          "    pd: coverpoint a;\n"
          "  endgroup\n"
          "  cg c = new(3);\n"
          "  cd d = new;\n"
          "  initial begin\n"
          "    a = 0; b = 0; c.sample(); d.sample();\n"
          "    a = 1; c.sample(); d.sample();\n"
          "    void'(c.p4.get_inst_coverage(n, m));\n"
          "    $display(\"%0.2f %0d %0d\", c.p4.get_inst_coverage(), n, m);\n"
          "    void'(c.pw.get_inst_coverage(n, m));\n"
          "    $display(\"%0.2f %0d %0d\", c.pw.get_inst_coverage(), n, m);\n"
          "    void'(c.pa.get_inst_coverage(n, m));\n"
          "    $display(\"%0.2f %0d %0d\", c.pa.get_inst_coverage(), n, m);\n"
          "    void'(d.pd.get_inst_coverage(n, m));\n"
          "    $display(\"%0.2f %0d %0d\", d.pd.get_inst_coverage(), n, m);\n"
          "  end\n"
          "endmodule\n"),
      "25.00 1 4\n"
      "25.00 1 4\n"
      "33.33 1 3\n"
      "50.00 1 2\n");
}

}  // namespace
