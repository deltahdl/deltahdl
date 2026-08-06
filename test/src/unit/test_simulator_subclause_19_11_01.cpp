#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "helpers_coverage_point_setup.h"
#include "simulator/coverage.h"

using namespace delta;

namespace {

// LRM 19.11.1: for user-defined bins the coverpoint coverage is the number of
// covered bins over the number of defined bins. Two defined bins with one
// covered gives 50%.
TEST(PointCoverage, UserDefinedBinsCoveredOverDefined) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = AddTwoValueBinPoint(g);

  db.Sample(g, {{"x", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 50.0);
}

// LRM 19.11.1: for automatically generated bins the denominator is
// MIN(auto_bin_max, 2^M) — exactly the number of bins AutoCreateBins produces
// (LRM 19.5.3). Covering 2 of the 4 auto bins gives 50%.
TEST(PointCoverage, AutoBinDenominatorIsAutoBinCount) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 3);  // M = 2 bits

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetPointCoverage(cp, covered, total);
  // The denominator is the shared N from LRM 19.5.3.
  EXPECT_EQ(static_cast<uint64_t>(total), CoverageDB::AutoBinCount(2, 4));

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 50.0);
}

// LRM 19.11.1: a bin with no associated value or transition is excluded from
// both the numerator and the denominator. After an auto bin is emptied (as
// ignore_bins would do, leaving "auto[]"), it no longer contributes; the
// remaining three bins, all covered, give 100%.
TEST(PointCoverage, EmptiedBinExcludedFromBothNumeratorAndDenominator) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 3);  // bins for 0, 1, 2, 3

  // Strip every value from the first bin, as applying ignore_bins to all of its
  // values would.
  cp->bins[0].values.clear();

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

// LRM 19.11.1: a coverpoint whose denominator is zero is reported by
// PointCoverageDenominatorZero. A bin with no associated value or transition
// does not count toward the denominator; a value bin does.
TEST(PointCoverage, DenominatorZeroDetection) {
  CoverPoint empty_cp;
  CoverBin no_value;
  no_value.name = "b0";  // no values, no transitions
  empty_cp.bins.push_back(no_value);
  EXPECT_TRUE(CoverageDB::PointCoverageDenominatorZero(&empty_cp));

  CoverPoint valued_cp;
  CoverBin valued;
  valued.name = "b0";
  valued.values = {0};
  valued_cp.bins.push_back(valued);
  EXPECT_FALSE(CoverageDB::PointCoverageDenominatorZero(&valued_cp));
}

// LRM 19.11.1: when the denominator is zero and the coverpoint's weight is
// nonzero, get_coverage returns 0.0.
TEST(PointCoverage, ZeroDenominatorNonzeroWeightReturnsZero) {
  CoverPoint cp;
  cp.weight = 1;
  CoverBin no_value;
  no_value.name = "b0";
  cp.bins.push_back(no_value);

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(&cp), 0.0);
}

// LRM 19.11.1: when the denominator is zero and the coverpoint's weight is
// zero, get_coverage returns 100.0.
TEST(PointCoverage, ZeroDenominatorZeroWeightReturns100) {
  CoverPoint cp;
  cp.weight = 0;
  CoverBin no_value;
  no_value.name = "b0";
  cp.bins.push_back(no_value);

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(&cp), 100.0);
}

// LRM 19.11.1: a coverpoint with a zero denominator does not contribute to the
// covergroup coverage computation — it is dropped from both the numerator and
// the denominator of the covergroup average. With the empty coverpoint dropped,
// the covergroup coverage is the surviving coverpoint's 100%, not 50%.
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
  no_value.name = "b0";  // no values: zero denominator
  CoverageDB::AddBin(empty, no_value);

  db.Sample(g, {{"keep", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 100.0);
}

// LRM 19.11.1: the ref-int pair form on a zero-denominator coverpoint reports
// zero for both the numerator and the denominator.
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

// LRM 19.11.1: in cumulative coverage, a bin's coverage threshold is the
// maximum of the at_least values of all instances (the conservative choice).
TEST(PointCoverage, CumulativeAtLeastIsMaxOverInstances) {
  EXPECT_EQ(CoverageDB::CumulativeAtLeast({1, 3, 2}), 3u);
  EXPECT_EQ(CoverageDB::CumulativeAtLeast({2, 2}), 2u);
  // With no instance values the default at_least of 1 applies.
  EXPECT_EQ(CoverageDB::CumulativeAtLeast({}), 1u);
}

// LRM 19.11.1: a bin is not considered covered until its hit count reaches the
// cumulative (maximum) at_least threshold. With a threshold of 3, two hits
// leave the bin uncovered (0%) and a third covers it (100%).
TEST(PointCoverage, BinCoveredOnlyAtCumulativeAtLeast) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin bin;
  bin.name = "b0";
  bin.values = {0};
  bin.at_least = CoverageDB::CumulativeAtLeast({1, 2, 3});  // max == 3
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 0.0);

  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

// LRM 19.11.1 (edge): a bin is excluded only when it has neither a value nor a
// transition. A transition bin, which has a transition but no value, therefore
// participates in the denominator and becomes covered once its transition
// completes.
TEST(PointCoverage, TransitionBinParticipatesInCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin trans;
  trans.name = "t";
  trans.kind = CoverBinKind::kTransition;
  trans.transitions = {{0, 1}};  // 0 => 1
  CoverageDB::AddBin(cp, trans);

  // The transition bin counts toward the denominator before it is hit.
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

// LRM 19.11.1 (edge): illegal, ignore, and default bins never participate in
// the coverage. A coverpoint built only from such bins has a zero denominator,
// so with a nonzero weight it reports 0.0.
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

// LRM 19.11.1 (edge): the weight-dependent result applies only when the
// denominator is zero. With participating bins present, an entirely uncovered
// coverpoint reports 0.0 from the |covered|/|defined| ratio even when its
// weight is zero — the zero-weight 100.0 rule does not apply here.
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

  // Nothing sampled: the denominator is nonzero (two defined bins) so coverage
  // is 0/2, not the zero-denominator zero-weight 100.0.
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 0.0);
}

}  // namespace
