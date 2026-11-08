#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
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

}  // namespace
