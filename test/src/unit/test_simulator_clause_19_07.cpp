#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

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

// LRM 19.7: specifying a value for the same option more than once within a
// covergroup definition is an error.
TEST(Coverage, DuplicateOptionInDefinitionIsError) {
  // No assignments and a single assignment cannot repeat an option.
  EXPECT_FALSE(CoverageDB::OptionSpecifiedMoreThanOnce({}));
  EXPECT_FALSE(
      CoverageDB::OptionSpecifiedMoreThanOnce({InstanceOptionKind::kWeight}));

  // Distinct options are fine.
  EXPECT_FALSE(CoverageDB::OptionSpecifiedMoreThanOnce(
      {InstanceOptionKind::kWeight, InstanceOptionKind::kGoal}));

  // Adjacent and non-adjacent repeats of the same option are both errors.
  EXPECT_TRUE(CoverageDB::OptionSpecifiedMoreThanOnce(
      {InstanceOptionKind::kGoal, InstanceOptionKind::kGoal}));
  EXPECT_TRUE(CoverageDB::OptionSpecifiedMoreThanOnce(
      {InstanceOptionKind::kWeight, InstanceOptionKind::kGoal,
       InstanceOptionKind::kWeight}));
}

// LRM 19.7, Table 19-2: instance options are restricted to particular
// syntactic levels. Every instance option may be set at the covergroup level;
// the coverpoint and cross levels accept only specific subsets.
TEST(Coverage, InstanceOptionSyntacticLevels) {
  const InstanceOptionKind all[] = {
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
  for (InstanceOptionKind kind : all) {
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

}  // namespace
