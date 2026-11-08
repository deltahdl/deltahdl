#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

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

}  // namespace
