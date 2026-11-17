#include <gtest/gtest.h>

#include <cstdint>
#include <cstdio>
#include <initializer_list>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_tagged_file.h"
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

TEST(Coverage, InstanceOptionsArePerInstance) {
  CoverageDB db;
  auto* g1 = db.CreateGroup("cg1");
  auto* g2 = db.CreateGroup("cg2");
  g1->options.goal = 80.0;

  EXPECT_DOUBLE_EQ(g1->options.goal, 80.0);
  EXPECT_DOUBLE_EQ(g2->options.goal, 100.0);
}

TEST(Coverage, WeightOptionMustBeNonNegative) {
  EXPECT_TRUE(CoverageDB::OptionWeightValid(0));
  EXPECT_TRUE(CoverageDB::OptionWeightValid(5));
  EXPECT_FALSE(CoverageDB::OptionWeightValid(-1));
}

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

  for (InstanceOptionKind kind :
       {InstanceOptionKind::kWeight, InstanceOptionKind::kGoal,
        InstanceOptionKind::kComment, InstanceOptionKind::kAtLeast}) {
    EXPECT_TRUE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCoverpoint));
    EXPECT_TRUE(CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCross));
  }

  for (InstanceOptionKind kind :
       {InstanceOptionKind::kAutoBinMax, InstanceOptionKind::kDetectOverlap}) {
    EXPECT_TRUE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCoverpoint));
    EXPECT_FALSE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCross));
  }

  for (InstanceOptionKind kind : {InstanceOptionKind::kCrossNumPrintMissing,
                                  InstanceOptionKind::kCrossRetainAutoBins}) {
    EXPECT_FALSE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCoverpoint));
    EXPECT_TRUE(CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCross));
  }

  for (InstanceOptionKind kind :
       {InstanceOptionKind::kName, InstanceOptionKind::kPerInstance,
        InstanceOptionKind::kGetInstCoverage}) {
    EXPECT_FALSE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCoverpoint));
    EXPECT_FALSE(
        CoverageDB::OptionAllowedAt(kind, CoverSyntacticLevel::kCross));
  }
}

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

TEST(CovergroupInstanceSim, NegativeWeightSetAtRunTimeIsReported) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] a;\n"
                       "  covergroup cg (int w);\n"
                       "    option.weight = w;\n"
                       "    cp: coverpoint a;\n"
                       "  endgroup\n"
                       "  cg c = new(-3);\n"
                       "  cg d = new(0);\n"
                       "  initial begin\n"
                       "    c.cp.option.weight = -4;\n"
                       "    c.cp.option.weight = 2;\n"
                       "    cg::type_option.weight = -5;\n"
                       "    cg::type_option.weight = 0;\n"
                       "    $display(\"%0d %0d %0d %0d\", c.option.weight, "
                       "c.cp.option.weight, d.option.weight, "
                       "cg::type_option.weight);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 2 0 0\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "the weight -3 is negative",
                            4, "19.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "the weight -4 is negative",
                            10, "19.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "the weight -5 is negative",
                            12, "19.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(CovergroupInstanceSim, ANegativeWeightWrittenAtEveryLevelIsReported) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] a, b;\n"
                 "  covergroup cg;\n"
                 "    ca: coverpoint a; cb: coverpoint b; x: cross ca, cb;\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    c.option.weight = -4;\n"
                 "    c.x.option.weight = -5; c.x.option.weight = 0;\n"
                 "    cg::ca::type_option.weight = -6;\n"
                 "    cg::ca::type_option.weight = 0;\n"
                 "    cg::x::type_option.weight = -7;\n"
                 "    cg::x::type_option.weight = 2;\n"
                 "    $display(\"%0d %0d %0d %0d\", c.option.weight,\n"
                 "             c.x.option.weight, "
                 "cg::ca::type_option.weight,\n"
                 "             cg::x::type_option.weight);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 0 0 2\n");
  for (auto [line, weight] :
       std::initializer_list<std::pair<uint32_t, const char*>>{
           {8u, "-4"}, {9u, "-5"}, {10u, "-6"}, {12u, "-7"}}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("the weight ") + weight + " is negative", line, "19.7"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(CovergroupInstanceSim, InstanceOptionsReadTheirDefaultsAtEveryLevel) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [1:0] v, y;\n"
          "  covergroup cg;\n"
          "    cp: coverpoint v; cy: coverpoint y; x: cross cp, cy;\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n"
          "    $display(\"%0d %0d [%s] %0d %0d %0d %0d %0d %0d %0d\",\n"
          "      c.option.weight, c.option.goal, c.option.comment,\n"
          "      c.option.at_least, c.option.auto_bin_max,\n"
          "      c.option.cross_num_print_missing,\n"
          "      c.option.cross_retain_auto_bins, c.option.detect_overlap,\n"
          "      c.option.per_instance, c.option.get_inst_coverage);\n"
          "    $display(\"%0d %0d [%s] %0d %0d %0d\", c.cp.option.weight,\n"
          "      c.cp.option.goal, c.cp.option.comment, c.cp.option.at_least,\n"
          "      c.cp.option.auto_bin_max, c.cp.option.detect_overlap);\n"
          "    $display(\"%0d %0d [%s] %0d %0d %0d\", c.x.option.weight,\n"
          "      c.x.option.goal, c.x.option.comment, c.x.option.at_least,\n"
          "      c.x.option.cross_num_print_missing,\n"
          "      c.x.option.cross_retain_auto_bins);\n"
          "  end\n"
          "endmodule\n",
          f),
      "1 100 [] 1 64 0 1 0 0 0\n1 100 [] 1 64 0\n1 100 [] 1 0 1\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, UnnamedInstancesReadDistinctNames) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  bit v;\n"
                       "  covergroup cg; coverpoint v; endgroup\n"
                       "  cg c = new;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  bit v;\n"
                       "  covergroup cg; coverpoint v; endgroup\n"
                       "  cg k = new, k2 = new;\n"
                       "  sub s1(); sub s2();\n"
                       "  initial $display(\"%0d %0d %0d\",\n"
                       "    k.option.name != k2.option.name,\n"
                       "    s1.c.option.name != s2.c.option.name,\n"
                       "    k.option.name != \"\");\n"
                       "endmodule\n",
                       f),
            "1 1 1\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, AnOptionTakesTheValuesHeldWhenItsInstanceIsBuilt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit v;\n"
                       "  int mv = 5;\n"
                       "  function int rd(); return mv * 2; endfunction\n"
                       "  covergroup cg (int w);\n"
                       "    option.weight = w;\n"
                       "    option.goal = mv;\n"
                       "    option.at_least = rd();\n"
                       "    coverpoint v;\n"
                       "  endgroup\n"
                       "  cg k, k2;\n"
                       "  initial begin\n"
                       "    k = new(2);\n"
                       "    mv = 7;\n"
                       "    k2 = new(5);\n"
                       "    mv = 9;\n"
                       "    $display(\"%0d %0d %0d %0d %0d %0d\", "
                       "k.option.weight,\n"
                       "      k2.option.weight, k.option.goal, "
                       "k2.option.goal,\n"
                       "      k.option.at_least, k2.option.at_least);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 5 5 7 10 14\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, AProceduralOptionWriteChangesOnlyItsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit v;\n"
                       "  covergroup cg;\n"
                       "    option.goal = 90;\n"
                       "    cp: coverpoint v;\n"
                       "  endgroup\n"
                       "  cg k = new, k2 = new;\n"
                       "  initial begin\n"
                       "    k.option.goal = 50; k2.cp.option.weight = 4;\n"
                       "    $display(\"%0d %0d %0d %0d\", k.option.goal, "
                       "k2.option.goal,\n"
                       "      k.cp.option.weight, k2.cp.option.weight);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "50 90 1 4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim,
     AtLeastSetInACoverpointBodyLeavesFewerHitsUncovered) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v;\n"
                 "  covergroup cg;\n"
                 "    cx: coverpoint v { option.at_least = 2; bins one = "
                 "{1}; }\n"
                 "    cy: coverpoint v { bins one = {1}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    v = 1; c.sample();\n"
                 "    $display(\"%0.2f %0.2f\", c.cx.get_inst_coverage(),\n"
                 "             c.cy.get_inst_coverage());\n"
                 "    c.sample();\n"
                 "    $display(\"%0.2f\", c.cx.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "0.00 100.00\n100.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, ProceduralGoalNameAndCrossPrintMissingReadBack) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit v, y;\n"
                 "  covergroup cg;\n"
                 "    cp: coverpoint v; cy: coverpoint y; x: cross cp, cy;\n"
                 "  endgroup\n"
                 "  cg k = new;\n"
                 "  initial begin\n"
                 "    k.option.goal = 50; k.option.name = \"nm\";\n"
                 "    k.x.option.cross_num_print_missing = 3;\n"
                 "    $display(\"%0d %s %0d\", k.option.goal, "
                 "k.option.name,\n"
                 "             k.x.option.cross_num_print_missing);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "50 nm 3\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CoverageOptionSim, AutoBinMaxSetAtTheCovergroupIsItsCoverpointsDefault) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [3:0] v, u;\n"
          "  covergroup cg; cp: coverpoint v; endgroup\n"
          "  covergroup cd;\n"
          "    option.auto_bin_max = 4;\n"
          "    cp: coverpoint v;\n"
          "    cq: coverpoint u { option.auto_bin_max = 2; }\n"
          "  endgroup\n"
          "  cg c = new; cd d = new;\n"
          "  initial begin\n"
          "    v = 0; u = 0; c.sample(); d.sample();\n"
          "    $display(\"%0.2f %0.2f %0.2f %0d\", c.cp.get_inst_coverage(),\n"
          "      d.cp.get_inst_coverage(), d.cq.get_inst_coverage(),\n"
          "      d.cp.option.auto_bin_max);\n"
          "  end\n"
          "endmodule\n",
          f),
      "6.25 25.00 50.00 4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CoverageOptionSim, OnlyTheDefaultingOptionsPassToCoverpointsAndCrosses) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module top;\n"
                "  bit [1:0] v, y;\n"
                "  covergroup cg;\n"
                "    cp: coverpoint v; cy: coverpoint y; x: cross cp, cy;\n"
                "  endgroup\n"
                "  covergroup cd;\n"
                "    option.cross_retain_auto_bins = 0;\n"
                "    option.weight = 3; option.goal = 70; option.comment = "
                "\"gc\";\n"
                "    cp: coverpoint v; cy: coverpoint y; x: cross cp, cy;\n"
                "  endgroup\n"
                "  cg c = new; cd d = new;\n"
                "  initial begin\n"
                "    $display(\"%0d %0d\", c.x.option.cross_retain_auto_bins,\n"
                "             d.x.option.cross_retain_auto_bins);\n"
                "    $display(\"%0d %0d [%s] %0d %0d [%s]\", "
                "d.cp.option.weight,\n"
                "      d.cp.option.goal, d.cp.option.comment, "
                "d.x.option.weight,\n"
                "      d.x.option.goal, d.x.option.comment);\n"
                "  end\n"
                "endmodule\n",
                f),
            "1 0\n1 100 [] 1 100 []\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CoverageOptionSim, AnInstanceWithoutPerInstanceStillFeedsItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v;\n"
                       "  covergroup cg;\n"
                       "    option.per_instance = 0;\n"
                       "    coverpoint v { bins b[] = {[0:3]}; }\n"
                       "  endgroup\n"
                       "  cg k = new, k2 = new;\n"
                       "  initial begin\n"
                       "    v = 0; k.sample(); v = 1; k2.sample(); v = 2; "
                       "k2.sample();\n"
                       "    $display(\"%0.2f\", cg::get_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "37.50\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CoverageOptionSim, GetInstCoverageWithMergedInstancesKeepsEachOwn) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [3:0] v;\n"
                 "  covergroup mg (bit gi);\n"
                 "    option.get_inst_coverage = gi;\n"
                 "    type_option.merge_instances = 1;\n"
                 "    px: coverpoint v { bins b1 = {1}; bins b2 = {2}; }\n"
                 "  endgroup\n"
                 "  covergroup ng (bit gi);\n"
                 "    option.get_inst_coverage = gi;\n"
                 "    px: coverpoint v { bins b1 = {1}; bins b2 = {2}; }\n"
                 "  endgroup\n"
                 "  mg g = new(1), h = new(0);\n"
                 "  ng n1 = new(1), n2 = new(0);\n"
                 "  initial begin\n"
                 "    v = 1; g.sample(); n1.sample();\n"
                 "    v = 2; h.sample(); n2.sample(); n2.sample();\n"
                 "    v = 1; n2.sample();\n"
                 "    $display(\"%0.2f %0.2f %0.2f\", mg::get_coverage(),\n"
                 "      g.get_inst_coverage(), h.get_inst_coverage());\n"
                 "    $display(\"%0.2f %0.2f %0.2f\", ng::get_coverage(),\n"
                 "      n1.get_inst_coverage(), n2.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "100.00 50.00 100.00\n75.00 50.00 100.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

static std::string SavedDatabase(const std::string& src,
                                 const std::string& name) {
  const std::string kPath = testing::TempDir() + name;
  SimFixture f;
  RunCapture(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  f.ctx.CoverageData().SaveCoverageDbFile(kPath);
  std::string text = ReadFileText(kPath);
  std::remove(kPath.c_str());
  return text;
}

TEST(CoverageOptionSim, AnInstanceWithPerInstanceIsSavedInTheDatabase) {
  const std::string kSaved = SavedDatabase(
      "module top;\n"
      "  bit [1:0] v;\n"
      "  covergroup cg;\n"
      "    option.per_instance = 1;\n"
      "    coverpoint v { bins lo = {0}; bins hi = {3}; }\n"
      "  endgroup\n"
      "  cg kfirst = new, ksecond = new;\n"
      "  initial begin\n"
      "    v = 0; kfirst.sample(); v = 3; ksecond.sample();\n"
      "  end\n"
      "endmodule\n",
      "delta_cov_19_07_per_instance.db");
  EXPECT_NE(kSaved.find("kfirst"), std::string::npos);
  EXPECT_NE(kSaved.find("ksecond"), std::string::npos);
}

TEST(CoverageOptionSim, DISABLED_AnInstancesGoalAndCommentAreSaved) {
  const std::string kSaved = SavedDatabase(
      "module top;\n"
      "  bit a, b;\n"
      "  covergroup cg;\n"
      "    option.goal = 83; option.comment = \"inst note\";\n"
      "    ca: coverpoint a { option.goal = 61; option.comment = \"cp note\"; "
      "}\n"
      "    cb: coverpoint b;\n"
      "    x: cross ca, cb { option.goal = 47; option.comment = \"x note\"; }\n"
      "  endgroup\n"
      "  cg c = new, c2 = new;\n"
      "  initial begin\n"
      "    c2.option.goal = 29; c2.option.comment = \"second note\";\n"
      "    a = 0; b = 0; c.sample();\n"
      "  end\n"
      "endmodule\n",
      "delta_cov_19_07_goal.db");
  for (const char* text : {"inst note", "cp note", "x note", "second note",
                           " 83", " 61", " 47", " 29"}) {
    EXPECT_NE(kSaved.find(text), std::string::npos) << text;
  }
}

TEST(CoverageOptionSim, MissingCrossBinsAreSavedInTheDatabase) {
  const std::string kSaved = SavedDatabase(
      "module top;\n"
      "  bit a, b;\n"
      "  covergroup cg;\n"
      "    ca: coverpoint a; cb: coverpoint b;\n"
      "    x: cross ca, cb { option.cross_num_print_missing = 2; "
      "}\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin a = 0; b = 0; c.sample(); end\n"
      "endmodule\n",
      "delta_cov_19_07_missing.db");
  EXPECT_NE(kSaved.find("<auto[0],auto[1]>"), std::string::npos);
  EXPECT_NE(kSaved.find("<auto[1],auto[0]>"), std::string::npos);
}

}  // namespace
