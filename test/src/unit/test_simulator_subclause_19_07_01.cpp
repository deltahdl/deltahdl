#include <gtest/gtest.h>

#include <cstdio>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_tagged_file.h"
#include "helpers_reported_error.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(CoverageTypeOptions, Defaults) {
  CoverGroupTypeOption to;
  EXPECT_EQ(to.weight, 1);
  EXPECT_EQ(to.goal, 100);
  EXPECT_TRUE(to.comment.empty());
  EXPECT_FALSE(to.strobe);
  EXPECT_FALSE(to.merge_instances);
  EXPECT_FALSE(to.distribute_first);
  EXPECT_DOUBLE_EQ(to.real_interval, 1.0);
}

TEST(CoverageTypeOptions, TypeCoverageWeightedAverage) {
  CoverageDB db;
  auto* g1 = db.CreateGroup("cg_1");
  g1->options.weight = 1;
  auto* p1 = CoverageDB::AddCoverPoint(g1, "x");
  CoverBin b1;
  b1.name = "b";
  b1.values = {0};
  CoverageDB::AddBin(p1, b1);
  db.Sample(g1, {{"x", 0}});

  auto* g2 = db.CreateGroup("cg_2");
  g2->options.weight = 1;
  auto* p2 = CoverageDB::AddCoverPoint(g2, "x");
  CoverBin b2;
  b2.name = "b";
  b2.values = {0};
  CoverageDB::AddBin(p2, b2);

  std::vector<const CoverGroup*> insts = {g1, g2};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, false), 50.0);
}

TEST(CoverageTypeOptions, TypeCoverageMergedUnion) {
  CoverageDB db;
  auto* g1 = db.CreateGroup("cg_1");
  auto* p1 = CoverageDB::AddCoverPoint(g1, "x");
  CoverBin b1a;
  b1a.name = "lo";
  b1a.values = {0};
  CoverageDB::AddBin(p1, b1a);
  CoverBin b1b;
  b1b.name = "hi";
  b1b.values = {1};
  CoverageDB::AddBin(p1, b1b);
  db.Sample(g1, {{"x", 0}});

  auto* g2 = db.CreateGroup("cg_2");
  auto* p2 = CoverageDB::AddCoverPoint(g2, "x");
  CoverBin b2a;
  b2a.name = "lo";
  b2a.values = {0};
  CoverageDB::AddBin(p2, b2a);
  CoverBin b2b;
  b2b.name = "hi";
  b2b.values = {1};
  CoverageDB::AddBin(p2, b2b);
  db.Sample(g2, {{"x", 1}});

  std::vector<const CoverGroup*> insts = {g1, g2};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, false), 50.0);
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, true), 100.0);
}

TEST(CoverageTypeOptions, AllowedSyntacticLevels) {
  using K = TypeOptionKind;
  using L = CoverSyntacticLevel;

  for (K k : {K::kWeight, K::kGoal, K::kComment}) {
    EXPECT_TRUE(CoverageDB::TypeOptionAllowedAt(k, L::kCovergroup));
    EXPECT_TRUE(CoverageDB::TypeOptionAllowedAt(k, L::kCoverpoint));
    EXPECT_TRUE(CoverageDB::TypeOptionAllowedAt(k, L::kCross));
  }

  for (K k : {K::kStrobe, K::kMergeInstances, K::kDistributeFirst}) {
    EXPECT_TRUE(CoverageDB::TypeOptionAllowedAt(k, L::kCovergroup));
    EXPECT_FALSE(CoverageDB::TypeOptionAllowedAt(k, L::kCoverpoint));
    EXPECT_FALSE(CoverageDB::TypeOptionAllowedAt(k, L::kCross));
  }

  EXPECT_TRUE(
      CoverageDB::TypeOptionAllowedAt(K::kRealInterval, L::kCovergroup));
  EXPECT_TRUE(
      CoverageDB::TypeOptionAllowedAt(K::kRealInterval, L::kCoverpoint));
  EXPECT_FALSE(CoverageDB::TypeOptionAllowedAt(K::kRealInterval, L::kCross));
}

TEST(CoverageTypeOptions, OnlyRealIntervalDefaultsDown) {
  using K = TypeOptionKind;
  EXPECT_TRUE(CoverageDB::TypeOptionDefaultsToLowerLevels(K::kRealInterval));
  for (K k : {K::kWeight, K::kGoal, K::kComment, K::kStrobe, K::kMergeInstances,
              K::kDistributeFirst}) {
    EXPECT_FALSE(CoverageDB::TypeOptionDefaultsToLowerLevels(k));
  }
}

TEST(CoverageTypeOptions, ProceduralSettability) {
  using K = TypeOptionKind;
  EXPECT_FALSE(CoverageDB::TypeOptionSettableProcedurally(K::kStrobe));
  EXPECT_FALSE(CoverageDB::TypeOptionSettableProcedurally(K::kRealInterval));
  for (K k : {K::kWeight, K::kGoal, K::kComment, K::kMergeInstances,
              K::kDistributeFirst}) {
    EXPECT_TRUE(CoverageDB::TypeOptionSettableProcedurally(k));
  }
}

TEST(CoverageTypeOptions, TypeCoverageNoInstances) {
  std::vector<const CoverGroup*> none;
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(none, false), 0.0);
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(none, true), 0.0);
}

TEST(CoverageTypeOptions, TypeCoverageZeroWeight) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg_1");
  g->options.weight = 0;
  auto* p = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b";
  b.values = {0};
  CoverageDB::AddBin(p, b);
  db.Sample(g, {{"x", 0}});

  std::vector<const CoverGroup*> insts = {g};
  EXPECT_DOUBLE_EQ(CoverageDB::ComputeTypeCoverage(insts, false), 0.0);
}

TEST(TypeOptionSim, ATypeOptionIsReadAndWrittenThroughTheType) {
  SimFixture f;
  auto out = RunCapture(
      "covergroup gc with function sample(bit a_var);\n"
      "  a : coverpoint a_var { type_option.weight = 3; bins one = {1}; }\n"
      "endgroup\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic gc g1 = new;\n"
      "    $display(\"%0d %0d\", gc::a::type_option.weight, "
      "gc::type_option.weight);\n"
      "    gc::type_option.weight = 5;\n"
      "    $display(\"%0d\", gc::type_option.weight);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1\n5\n");
}

TEST(TypeOptionSim, ATypeOptionReadsThroughTheTypeBeforeAnyInstance) {
  SimFixture f;
  auto out = RunCapture(
      "covergroup gc with function sample(bit a_var);\n"
      "  type_option.comment = \"def\";\n"
      "  a : coverpoint a_var { type_option.weight = 3; }\n"
      "  x : cross a, a_var { type_option.goal = 90; }\n"
      "endgroup\n"
      "module t;\n"
      "  initial begin\n"
      "    $display(\"%0d %0d %s %0d\", gc::a::type_option.weight,\n"
      "             gc::type_option.goal, gc::type_option.comment,\n"
      "             gc::x::type_option.goal);\n"
      "    gc::a::type_option.goal = 80;\n"
      "    gc::type_option.comment = \"set\";\n"
      "    gc::type_option.strobe = 1;\n"
      "    $display(\"%0d %s %0d %0d\", gc::a::type_option.goal,\n"
      "             gc::type_option.comment, gc::type_option.strobe,\n"
      "             gc::zz::type_option.goal);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 100 def 90\n80 set 0 0\n");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "type option 'strobe' can be set only in the covergroup definition", 13,
      "19.7.1"));
}

TEST(TypeOptionSim, ATypeOptionWrittenBeforeAnInstanceHoldsForIt) {
  SimFixture f;
  auto out = RunCapture(
      "covergroup gc with function sample(bit a_var, bit b_var);\n"
      "  a : coverpoint a_var;\n"
      "  x : cross a_var, b_var;\n"
      "endgroup\n"
      "covergroup go with function sample(bit v);\n"
      "  coverpoint v;\n"
      "endgroup\n"
      "module t;\n"
      "  initial begin\n"
      "    gc::type_option.comment = \"all\";\n"
      "    gc::a::type_option.weight = 3;\n"
      "    gc::x::type_option.goal = 70;\n"
      "    begin\n"
      "      automatic go o = new;\n"
      "      automatic gc g1 = new;\n"
      "      $display(\"%s %0d %0d %0d\", gc::type_option.comment,\n"
      "               gc::a::type_option.weight, gc::x::type_option.goal,\n"
      "               gc::zz::type_option.goal);\n"
      "      gc::x::type_option.weight = 4;\n"
      "      $display(\"%0d [%s]\", gc::x::type_option.weight,\n"
      "               go::type_option.comment);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "all 3 70 0\n4 []\n");
}

TEST(TypeOptionSim, MergeDistributeAndRealIntervalReadTheirDefaults) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  real r;\n"
                       "  covergroup cg; cr: coverpoint r { bins b = "
                       "{[0.0:1.0]}; } endgroup\n"
                       "  cg c = new;\n"
                       "  initial $display(\"%0d %0d %0.1f %0.1f\",\n"
                       "    cg::type_option.merge_instances,\n"
                       "    cg::type_option.distribute_first,\n"
                       "    cg::type_option.real_interval,\n"
                       "    cg::cr::type_option.real_interval);\n"
                       "endmodule\n",
                       f),
            "0 0 1.0 1.0\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(TypeOptionSim, DistributeFirstWrittenProcedurallyHolds) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit v;\n"
                 "  covergroup cg; coverpoint v; endgroup\n"
                 "  initial begin\n"
                 "    cg::type_option.distribute_first = 1;\n"
                 "    $display(\"%0d\", cg::type_option.distribute_first);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(TypeOptionSim, ACovergroupRealIntervalIsItsCoverpointsDefault) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  real r;\n"
                 "  covergroup cg;\n"
                 "    type_option.real_interval = 0.5;\n"
                 "    cr: coverpoint r { bins s[] = {[1.0:3.0]}; }\n"
                 "    cw: coverpoint r { type_option.real_interval = 2.0;\n"
                 "      bins s[] = {[1.0:3.0]}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    r = 1.2; c.sample();\n"
                 "    $display(\"%0.1f %0.1f %0.2f %0.2f\",\n"
                 "      cg::cr::type_option.real_interval,\n"
                 "      cg::cw::type_option.real_interval,\n"
                 "      c.cr.get_inst_coverage(), c.cw.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "0.5 2.0 25.00 100.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(TypeOptionSim, CovergroupTypeWeightGoalAndCommentDoNotPassDown) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] a, b;\n"
                 "  covergroup cg;\n"
                 "    type_option.weight = 4; type_option.goal = 60;\n"
                 "    type_option.comment = \"t\";\n"
                 "    ca: coverpoint a; cb: coverpoint b; x: cross ca, cb;\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial $display(\"%0d %0d [%s] %0d %0d [%s]\",\n"
                 "    cg::ca::type_option.weight, cg::ca::type_option.goal,\n"
                 "    cg::ca::type_option.comment, cg::x::type_option.weight,\n"
                 "    cg::x::type_option.goal, cg::x::type_option.comment);\n"
                 "endmodule\n",
                 f),
      "1 100 [] 1 100 []\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(TypeCoverageSim, MergeInstancesOffAveragesInstancesByTheirWeights) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [3:0] v;\n"
                 "  covergroup ng (int w);\n"
                 "    option.weight = w;\n"
                 "    px: coverpoint v { bins b1 = {1}; bins b2 = {2};\n"
                 "      bins b3 = {3}; bins b4 = {4}; }\n"
                 "  endgroup\n"
                 "  ng n1 = new(1), n2 = new(3);\n"
                 "  initial begin\n"
                 "    v = 1; n1.sample();\n"
                 "    for (int i = 1; i <= 4; i++) begin v = i; n2.sample(); "
                 "end\n"
                 "    $display(\"%0.2f %0.2f %0.2f\", ng::get_coverage(),\n"
                 "      n1.get_inst_coverage(), n2.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "81.25 25.00 100.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(TypeCoverageSim, ACrossTypeWeightWeighsItInTypeCoverageAlone) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit a, b;\n"
                       "  covergroup cg;\n"
                       "    option.get_inst_coverage = 1;\n"
                       "    type_option.merge_instances = 1;\n"
                       "    ca: coverpoint a { bins one = {1}; }\n"
                       "    cb: coverpoint b { bins one = {1}; }\n"
                       "    x: cross ca, cb { type_option.weight = 3; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    a = 1; b = 0; c.sample();\n"
                       "    $display(\"%0.2f %0.2f\", cg::get_coverage(),\n"
                       "             c.get_inst_coverage());\n"
                       "    cg::x::type_option.weight = 0;\n"
                       "    $display(\"%0.2f\", cg::get_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "20.00 33.33\n50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(TypeCoverageSim, DISABLED_ACovergroupTypeWeightWeighsItInGlobalCoverage) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit a;\n"
                       "  covergroup g1;\n"
                       "    type_option.weight = 3;\n"
                       "    p: coverpoint a { bins one = {1}; }\n"
                       "  endgroup\n"
                       "  covergroup g2;\n"
                       "    option.weight = 5;\n"
                       "    p: coverpoint a { bins zero = {0}; }\n"
                       "  endgroup\n"
                       "  g1 k1 = new; g2 k2 = new;\n"
                       "  initial begin\n"
                       "    a = 1; k1.sample(); k2.sample();\n"
                       "    $display(\"%0.2f\", $get_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "75.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(TypeOptionSim, DISABLED_ATypesGoalAndCommentAreSaved) {
  const std::string kPath = testing::TempDir() + "delta_cov_19_07_01_goal.db";
  SimFixture f;
  RunCapture(
      "module top;\n"
      "  bit a, b;\n"
      "  covergroup cg;\n"
      "    option.comment = \"inst note\";\n"
      "    type_option.goal = 73; type_option.comment = \"group note\";\n"
      "    ca: coverpoint a { type_option.goal = 64; }\n"
      "    cb: coverpoint b;\n"
      "    x: cross ca, cb { type_option.comment = \"x type note\"; }\n"
      "  endgroup\n"
      "  covergroup cd; type_option.comment = \"other type\"; coverpoint a; "
      "endgroup\n"
      "  cg c = new; cd d = new;\n"
      "  initial begin\n"
      "    cg::x::type_option.goal = 52; cg::cb::type_option.comment = \"cb "
      "type note\";\n"
      "    a = 0; b = 0; c.sample(); d.sample();\n"
      "  end\n"
      "endmodule\n",
      f);
  f.ctx.CoverageData().SaveCoverageDbFile(kPath);
  const std::string kSaved = ReadFileText(kPath);
  std::remove(kPath.c_str());
  for (const char* text : {"group note", "x type note", "cb type note",
                           "other type", " 73", " 64", " 52"}) {
    EXPECT_NE(kSaved.find(text), std::string::npos) << text;
  }
}

}  // namespace
