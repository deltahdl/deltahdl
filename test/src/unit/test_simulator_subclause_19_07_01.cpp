#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// LRM 19.7.1, Table 19-3: default values of the covergroup type options.
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

// LRM 19.7.1: with merge_instances false, type coverage is the weighted average
// of the per-instance coverage.
TEST(CoverageTypeOptions, TypeCoverageWeightedAverage) {
  CoverageDB db;
  // Instance 1: one bin, covered.
  auto* g1 = db.CreateGroup("cg_1");
  g1->options.weight = 1;
  auto* p1 = CoverageDB::AddCoverPoint(g1, "x");
  CoverBin b1;
  b1.name = "b";
  b1.values = {0};
  CoverageDB::AddBin(p1, b1);
  db.Sample(g1, {{"x", 0}});

  // Instance 2: one bin, not covered.
  auto* g2 = db.CreateGroup("cg_2");
  g2->options.weight = 1;
  auto* p2 = CoverageDB::AddCoverPoint(g2, "x");
  CoverBin b2;
  b2.name = "b";
  b2.values = {0};
  CoverageDB::AddBin(p2, b2);

  std::vector<const CoverGroup*> insts = {g1, g2};
  // 100% and 0% averaged equally -> 50%.
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/false), 50.0);
}

// LRM 19.7.1: with merge_instances true, type coverage is the union of coverage
// across instances -- a bin covered in any instance counts as covered.
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
  db.Sample(g1, {{"x", 0}});  // covers "lo" only

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
  db.Sample(g2, {{"x", 1}});  // covers "hi" only

  std::vector<const CoverGroup*> insts = {g1, g2};
  // Neither instance alone reaches 100%, but the union covers both bins.
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/false), 50.0);
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/true), 100.0);
}

// LRM 19.7.1, Table 19-4: syntactic levels at which each type option is
// allowed.
TEST(CoverageTypeOptions, AllowedSyntacticLevels) {
  using K = TypeOptionKind;
  using L = CoverSyntacticLevel;

  // weight/goal/comment are allowed everywhere.
  for (K k : {K::kWeight, K::kGoal, K::kComment}) {
    EXPECT_TRUE(CoverageDB::TypeOptionAllowedAt(k, L::kCovergroup));
    EXPECT_TRUE(CoverageDB::TypeOptionAllowedAt(k, L::kCoverpoint));
    EXPECT_TRUE(CoverageDB::TypeOptionAllowedAt(k, L::kCross));
  }

  // strobe/merge_instances/distribute_first: covergroup only.
  for (K k : {K::kStrobe, K::kMergeInstances, K::kDistributeFirst}) {
    EXPECT_TRUE(CoverageDB::TypeOptionAllowedAt(k, L::kCovergroup));
    EXPECT_FALSE(CoverageDB::TypeOptionAllowedAt(k, L::kCoverpoint));
    EXPECT_FALSE(CoverageDB::TypeOptionAllowedAt(k, L::kCross));
  }

  // real_interval: covergroup and coverpoint, not cross.
  EXPECT_TRUE(
      CoverageDB::TypeOptionAllowedAt(K::kRealInterval, L::kCovergroup));
  EXPECT_TRUE(
      CoverageDB::TypeOptionAllowedAt(K::kRealInterval, L::kCoverpoint));
  EXPECT_FALSE(CoverageDB::TypeOptionAllowedAt(K::kRealInterval, L::kCross));
}

// LRM 19.7.1: only real_interval propagates as a default to lower syntactic
// levels when set at the covergroup level.
TEST(CoverageTypeOptions, OnlyRealIntervalDefaultsDown) {
  using K = TypeOptionKind;
  EXPECT_TRUE(CoverageDB::TypeOptionDefaultsToLowerLevels(K::kRealInterval));
  for (K k : {K::kWeight, K::kGoal, K::kComment, K::kStrobe, K::kMergeInstances,
              K::kDistributeFirst}) {
    EXPECT_FALSE(CoverageDB::TypeOptionDefaultsToLowerLevels(k));
  }
}

// LRM 19.7.1: strobe and real_interval may be set only in the covergroup
// definition; other type options may also be assigned procedurally.
TEST(CoverageTypeOptions, ProceduralSettability) {
  using K = TypeOptionKind;
  EXPECT_FALSE(CoverageDB::TypeOptionSettableProcedurally(K::kStrobe));
  EXPECT_FALSE(CoverageDB::TypeOptionSettableProcedurally(K::kRealInterval));
  for (K k : {K::kWeight, K::kGoal, K::kComment, K::kMergeInstances,
              K::kDistributeFirst}) {
    EXPECT_TRUE(CoverageDB::TypeOptionSettableProcedurally(k));
  }
}

// LRM 19.7.1 (edge case): type coverage over no instances is zero, in both the
// weighted-average and merged modes.
TEST(CoverageTypeOptions, TypeCoverageNoInstances) {
  std::vector<const CoverGroup*> none;
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(none, /*merge_instances=*/false), 0.0);
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(none, /*merge_instances=*/true), 0.0);
}

// LRM 19.7.1 (edge case): a weighted-average type coverage where every instance
// weight is zero is zero (no division by a zero weight sum).
TEST(CoverageTypeOptions, TypeCoverageZeroWeight) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg_1");
  g->options.weight = 0;
  auto* p = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b";
  b.values = {0};
  CoverageDB::AddBin(p, b);
  db.Sample(g, {{"x", 0}});  // the lone bin is covered

  std::vector<const CoverGroup*> insts = {g};
  EXPECT_DOUBLE_EQ(
      CoverageDB::ComputeTypeCoverage(insts, /*merge_instances=*/false), 0.0);
}

}  // namespace
