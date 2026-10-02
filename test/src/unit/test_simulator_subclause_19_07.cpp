#include <gtest/gtest.h>

#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, AtLeastOption) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin bin;
  bin.name = "b0";
  bin.values = {0};
  bin.at_least = 3;
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 0.0);

  db.Sample(g, {{"x", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(Coverage, WeightOption) {
  CoverageDB db;
  auto* g1 = db.CreateGroup("cg1");
  g1->options.weight = 2;
  auto* cp1 = CoverageDB::AddCoverPoint(g1, "x");
  CoverBin b1;
  b1.name = "b";
  b1.values = {0};
  CoverageDB::AddBin(cp1, b1);
  db.Sample(g1, {{"x", 0}});

  auto* g2 = db.CreateGroup("cg2");
  g2->options.weight = 1;
  auto* cp2 = CoverageDB::AddCoverPoint(g2, "y");
  CoverBin b2;
  b2.name = "b";
  b2.values = {0};
  CoverageDB::AddBin(cp2, b2);

  double global = db.GetGlobalCoverage();
  EXPECT_NEAR(global, 200.0 / 3.0, 0.01);
}

TEST(Coverage, AutoBinMaxControl) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 8;
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");

  EXPECT_EQ(cp->auto_bin_count, 8u);
}

// LRM 19.7, Table 19-1: a newly instantiated covergroup carries the default
// values listed for each instance-specific option.
TEST(Coverage, InstanceOptionDefaults) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  const CoverOptions& o = g->options;

  EXPECT_EQ(o.weight, 1u);
  EXPECT_DOUBLE_EQ(o.goal, 100.0);
  EXPECT_TRUE(o.comment.empty());
  EXPECT_EQ(o.at_least, 1u);
  EXPECT_EQ(o.auto_bin_max, 64u);
  EXPECT_EQ(o.cross_num_print_missing, 0);
  EXPECT_TRUE(o.cross_retain_auto_bins);
  EXPECT_FALSE(o.detect_overlap);
  EXPECT_FALSE(o.per_instance);
  EXPECT_FALSE(o.get_inst_coverage);
}

// LRM 19.7: each instance can initialize an instance option to its own value,
// affecting only that instance.
TEST(Coverage, InstanceOptionsArePerInstance) {
  CoverageDB db;
  auto* g1 = db.CreateGroup("cg1");
  auto* g2 = db.CreateGroup("cg2");
  g1->options.goal = 80.0;

  EXPECT_DOUBLE_EQ(g1->options.goal, 80.0);
  EXPECT_DOUBLE_EQ(g2->options.goal, 100.0);
}

// LRM 19.7, Table 19-1: the weight option shall be a non-negative integral
// value.
TEST(Coverage, WeightOptionMustBeNonNegative) {
  EXPECT_TRUE(CoverageDB::OptionWeightValid(0));
  EXPECT_TRUE(CoverageDB::OptionWeightValid(5));
  EXPECT_FALSE(CoverageDB::OptionWeightValid(-1));
}

// LRM 19.7, Table 19-2: instance options are restricted to particular
// syntactic levels. Every instance option may be set at the covergroup level;
// the coverpoint and cross levels accept only specific subsets.
TEST(Coverage, InstanceOptionSyntacticLevels) {
  const InstanceOptionKind kAll[] = {
      InstanceOptionKind::kName,
      InstanceOptionKind::kWeight,
      InstanceOptionKind::kGoal,
      InstanceOptionKind::kComment,
      InstanceOptionKind::kAtLeast,
      InstanceOptionKind::kAutoBinMax,
      InstanceOptionKind::kCrossNumPrintMissing,
      InstanceOptionKind::kCrossRetainAutoBins,
      InstanceOptionKind::kDetectOverlap,
      InstanceOptionKind::kPerInstance,
      InstanceOptionKind::kGetInstCoverage,
  };
  for (InstanceOptionKind kind : kAll) {
    EXPECT_TRUE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCovergroup));
  }

  // weight, goal, comment, at_least: allowed at all three levels.
  for (InstanceOptionKind kind :
       {InstanceOptionKind::kWeight, InstanceOptionKind::kGoal,
        InstanceOptionKind::kComment, InstanceOptionKind::kAtLeast}) {
    EXPECT_TRUE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCoverpoint));
    EXPECT_TRUE(CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCross));
  }

  // auto_bin_max and detect_overlap: coverpoint yes, cross no.
  for (InstanceOptionKind kind :
       {InstanceOptionKind::kAutoBinMax, InstanceOptionKind::kDetectOverlap}) {
    EXPECT_TRUE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCoverpoint));
    EXPECT_FALSE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCross));
  }

  // cross_num_print_missing and cross_retain_auto_bins: cross yes, coverpoint
  // no.
  for (InstanceOptionKind kind : {InstanceOptionKind::kCrossNumPrintMissing,
                                  InstanceOptionKind::kCrossRetainAutoBins}) {
    EXPECT_FALSE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCoverpoint));
    EXPECT_TRUE(CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCross));
  }

  // name, per_instance, get_inst_coverage: covergroup level only.
  for (InstanceOptionKind kind :
       {InstanceOptionKind::kName, InstanceOptionKind::kPerInstance,
        InstanceOptionKind::kGetInstCoverage}) {
    EXPECT_FALSE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCoverpoint));
    EXPECT_FALSE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCross));
  }
}

// LRM 19.7: covergroup-level options act as defaults for lower levels except
// weight, goal, comment, and per_instance. The covergroup-only options (name,
// get_inst_coverage) likewise do not propagate.
TEST(Coverage, InstanceOptionDefaultPropagation) {
  for (InstanceOptionKind kind :
       {InstanceOptionKind::kAtLeast, InstanceOptionKind::kAutoBinMax,
        InstanceOptionKind::kCrossNumPrintMissing,
        InstanceOptionKind::kCrossRetainAutoBins,
        InstanceOptionKind::kDetectOverlap}) {
    EXPECT_TRUE(CoverageDB::OptionDefaultsToLowerLevels(kind));
  }

  for (InstanceOptionKind kind :
       {InstanceOptionKind::kName, InstanceOptionKind::kWeight,
        InstanceOptionKind::kGoal, InstanceOptionKind::kComment,
        InstanceOptionKind::kPerInstance,
        InstanceOptionKind::kGetInstCoverage}) {
    EXPECT_FALSE(CoverageDB::OptionDefaultsToLowerLevels(kind));
  }
}

// LRM 19.7: per_instance and get_inst_coverage are definition-only;
// auto_bin_max, detect_overlap, and cross_retain_auto_bins are
// covergroup/coverpoint definition-only; the rest may be set procedurally.
TEST(Coverage, InstanceOptionProceduralSettability) {
  for (InstanceOptionKind kind :
       {InstanceOptionKind::kPerInstance, InstanceOptionKind::kGetInstCoverage,
        InstanceOptionKind::kAutoBinMax, InstanceOptionKind::kDetectOverlap,
        InstanceOptionKind::kCrossRetainAutoBins}) {
    EXPECT_FALSE(CoverageDB::OptionSettableProcedurally(kind));
  }

  for (InstanceOptionKind kind :
       {InstanceOptionKind::kName, InstanceOptionKind::kWeight,
        InstanceOptionKind::kGoal, InstanceOptionKind::kComment,
        InstanceOptionKind::kAtLeast,
        InstanceOptionKind::kCrossNumPrintMissing}) {
    EXPECT_TRUE(CoverageDB::OptionSettableProcedurally(kind));
  }
}

// §19.7: an option assignment in the definition takes effect when the
// covergroup is instantiated; at_least = 2 leaves the bin hit once uncovered.
TEST(CovergroupInstanceSim, AtLeastSetInDefinitionAppliesToInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module top;\n"
                "  bit [1:0] v;\n"
                "  covergroup cg;\n"
                "    option.at_least = 2;\n"
                "    coverpoint v { bins lo = {0}; bins hi = {3}; }\n"
                "  endgroup\n"
                "  cg c = new;\n"
                "  initial begin\n"
                "    v = 0; c.sample(); v = 3; c.sample(); v = 3; c.sample();\n"
                "    $display(\"cov=%0.2f\", c.get_inst_coverage());\n"
                "  end\n"
                "endmodule\n",
                f),
            "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.7 and §19.10: option is a member of every instance, so c.option.at_least
// reads the value the definition gave it.
TEST(CovergroupInstanceSim, OptionReadThroughInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v;\n"
                       "  covergroup cg;\n"
                       "    option.at_least = 2;\n"
                       "    coverpoint v { bins lo = {0}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial $display(\"al=%0d\", c.option.at_least);\n"
                       "endmodule\n",
                       f),
            "al=2\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.7: an instance option other than per_instance, get_inst_coverage,
// auto_bin_max, detect_overlap and cross_retain_auto_bins may be assigned after
// instantiation, at the covergroup level or at a coverpoint's.
TEST(CovergroupInstanceSim, ProceduralOptionWritesSetTheInstanceOptions) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module top;\n"
                "  bit [1:0] v;\n"
                "  covergroup cg; a: coverpoint v { bins lo = {0}; } endgroup\n"
                "  cg c = new;\n"
                "  initial begin\n"
                "    c.option.comment = \"hello\"; c.a.option.weight = 3;\n"
                "    $display(\"comment=%s weight=%0d\", c.option.comment, "
                "c.a.option.weight);\n"
                "  end\n"
                "endmodule\n",
                f),
            "comment=hello weight=3\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.7: an instance option may be assigned procedurally after the covergroup
// is built, and one set at the covergroup level is the default of each of its
// coverpoints that sets none of its own: at_least 2 on e, as on c's cx itself
// and in d's definition, leaves one hit short of covering the bin. Assigned
// to e, it was held but its coverpoint counted the bin after one hit.
TEST(CoverageOptionSim,
     ACovergroupOptionAssignedProcedurallyIsItsItemsDefault) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  covergroup cg with function sample(bit x);\n"
      "    cx: coverpoint x { bins one = {1}; }\n"
      "  endgroup\n"
      "  covergroup cd with function sample(bit x);\n"
      "    option.at_least = 2;\n"
      "    cx: coverpoint x { bins one = {1}; }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  cg e = new;\n"
      "  cd d = new;\n"
      "  initial begin\n"
      "    c.cx.option.at_least = 2;\n"
      "    e.option.at_least = 2;\n"
      "    c.sample(1); e.sample(1); d.sample(1);\n"
      "    $display(\"%0.2f %0.2f %0.2f %0d %0d\", c.get_inst_coverage(), "
      "e.get_inst_coverage(), d.get_inst_coverage(), c.cx.option.at_least, "
      "e.option.at_least);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0.00 0.00 0.00 2 2\n");
}

// §19.7: a covergroup-level option assigned procedurally is the default of
// each cross that does not set its own: xy sets at_least 1 in its definition
// and covers its bin after one hit, while yx takes the covergroup's 2. A
// cross's own option, yx's weight, written after instantiation, is its own.
TEST(CoverageOptionSim,
     ACovergroupOptionAssignedProcedurallyIsItsCrossesDefault) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  covergroup cg with function sample(bit x, bit y);\n"
      "    cx: coverpoint x { bins one = {1}; }\n"
      "    cy: coverpoint y { bins one = {1}; }\n"
      "    xy: cross cx, cy { option.at_least = 1; type_option.weight = 2; }\n"
      "    yx: cross cx, cy;\n"
      "  endgroup\n"
      "  cg e = new;\n"
      "  initial begin\n"
      "    e.option.at_least = 2;\n"
      "    e.yx.option.weight = 2;\n"
      "    e.sample(1, 1);\n"
      "    $display(\"%0.2f %0.2f %0d\", e.xy.get_inst_coverage(),\n"
      "             e.yx.get_inst_coverage(), e.yx.option.weight);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "100.00 0.00 2\n");
}

// §19.7, Table 19-1: with detect_overlap true, two bins of a coverpoint whose
// range lists share a value draw a warning, an array's bin among them and two
// intervals of a real coverpoint (§19.5.1), while an ignore_bins sharing
// values with a bin draws none, and neither does a coverpoint that leaves the
// option at its default of 0.
TEST(CoverageOptionSim, DetectOverlapWarnsOfOverlappingRangeLists) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  bit [3:0] x; real r;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x { option.detect_overlap = 1;\n"
      "      bins lo = {[0:5]}; bins hi = {[3:8]};\n"
      "      bins top = {9, 10}; bins s[] = {10, 11}; ignore_bins ig = {0}; }\n"
      "    b: coverpoint x { bins lo = {[0:5]}; bins hi = {[3:8]}; }\n"
      "    c: coverpoint r { option.detect_overlap = 1; bins lo = "
      "{[1.0:3.0]};\n"
      "      bins hi = {[2.0:4.0]}; bins far = {[5.0:6.0]}; }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin x = 4; c.sample(); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bins 'lo' and 'hi' of coverpoint 'a' overlap "
                              "in their range lists",
                              5, "19.7"));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bins 'top' and 's[10]' of coverpoint 'a' "
                              "overlap in their range lists",
                              6, "19.7"));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bins 'lo' and 'hi' of coverpoint 'c' overlap "
                              "in their range lists",
                              9, "19.7"));
  EXPECT_EQ(f.diag.WarningCount(), 3u);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.7, Table 19-1: with detect_overlap true, two transition bins whose
// transition lists share a transition draw a warning; §19.5.2 expands
// `0, 1 => 2` into `0 => 2` and `1 => 2`. The option set on the covergroup is
// each coverpoint's default, and an ignore_bins transition draws none.
TEST(CoverageOptionSim, DetectOverlapWarnsOfOverlappingTransitionLists) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  bit [3:0] x;\n"
      "  covergroup cg;\n"
      "    option.detect_overlap = 1;\n"
      "    a: coverpoint x { bins t1 = (1 => 2); bins t2 = (0, 1 => 2);\n"
      "      bins t3 = (3 => 4); ignore_bins it = (3 => 4); }\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin x = 1; c.sample(); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "bins 't1' and 't2' of coverpoint 'a' overlap "
                              "in their transition lists",
                              5, "19.7"));
  EXPECT_EQ(f.diag.WarningCount(), 1u);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.7, Table 19-1: cross_num_print_missing is how many of a cross's missing
// cross bins the coverage report lists, 0 by default listing none. ab sets 2
// of its 3 missing; the covergroup-level 1 of cg2 is xy's default, and pq,
// whose one bin is covered, has none to list; ba keeps 0.
TEST(CoverageOptionSim, CrossNumPrintMissingListsThatManyMissingBins) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  bit x, y;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    ab: cross a, b { option.cross_num_print_missing = 2; }\n"
      "    ba: cross b, a;\n"
      "  endgroup\n"
      "  covergroup cg2;\n"
      "    option.cross_num_print_missing = 1;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    xy: cross a, b;\n"
      "    p: coverpoint x { bins one = {1}; }\n"
      "    q: coverpoint y { bins one = {1}; }\n"
      "    pq: cross p, q;\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  cg2 c2 = new;\n"
      "  initial begin\n"
      "    x = 0; y = 0; c.sample(); c2.sample();\n"
      "    x = 1; y = 1; c2.sample();\n"
      "  end\n"
      "endmodule\n",
      f);
  std::ostringstream report;
  f.ctx.CoverageData().ReportMissingCrossBins(report);
  EXPECT_EQ(report.str(),
            "cross c.ab: 3 cross bins missing\n"
            "  <auto[0],auto[1]>\n"
            "  <auto[1],auto[0]>\n"
            "cross c2.xy: 2 cross bins missing\n"
            "  <auto[0],auto[1]>\n");
}

}  // namespace
