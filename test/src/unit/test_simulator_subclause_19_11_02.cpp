#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// Builds a 2x2 cross "ab" over coverpoints a and b (each with bins {0},{1})
// inside a fresh group on the caller-owned db, auto-creates the cross bins, and
// returns the cross. The group is reported through out_group so callers can
// sample it.
CrossCover* BuildTwoByTwoCross(CoverageDB& db, CoverGroup*& out_group) {
  auto* g = db.CreateGroup("cg");
  auto* a = CoverageDB::AddCoverPoint(g, "a");
  CoverBin a0;
  a0.name = "a0";
  a0.values = {0};
  CoverageDB::AddBin(a, a0);
  CoverBin a1;
  a1.name = "a1";
  a1.values = {1};
  CoverageDB::AddBin(a, a1);

  auto* b = CoverageDB::AddCoverPoint(g, "b");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(b, b0);
  CoverBin b1;
  b1.name = "b1";
  b1.values = {1};
  CoverageDB::AddBin(b, b1);

  CrossCover cross;
  cross.name = "ab";
  cross.coverpoint_names = {"a", "b"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));
  CoverageDB::AutoCreateCrossBins(g, xc);

  out_group = g;
  return xc;
}

// LRM 19.11.2: the auto-cross bin count B_c is the product of the crossed
// coverpoints' bin cardinalities, ∏ B_j, less the cross products B_b comprised
// by user-defined cross bins. With cardinalities 3 and 2 and two products taken
// by user-defined bins, B_c = 3*2 - 2 = 4.
TEST(CrossCoverage, AutoBinCountIsProductMinusUserProducts) {
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({3, 2}, 2), 4u);
  // With no user-defined cross bins B_b is zero, so B_c is the full product.
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({3, 2}, 0), 6u);
  // A crossed coverpoint with no bins makes the product, and B_c, zero.
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({3, 0}, 0), 0u);
}

// LRM 19.11.2: the cross coverage denominator is B_c + B_u. With cardinalities
// 3 and 2, two products comprised by user-defined bins (B_c = 4) and one
// significant user-defined cross bin (B_u = 1), the denominator is 5.
TEST(CrossCoverage, DenominatorIsAutoBinsPlusUserBins) {
  EXPECT_EQ(CoverageDB::CrossCoverageDenominator({3, 2}, 2, 1), 5u);
  // Pure auto cross: denominator is the full product ∏ B_j.
  EXPECT_EQ(CoverageDB::CrossCoverageDenominator({3, 2}, 0, 0), 6u);
}

// LRM 19.11.2: B_u counts only significant user-defined cross bins — those that
// contribute toward coverage. A cross product selected by ignore_bins or
// illegal_bins contributes no coverage bin and so does not raise B_u; only a
// counting outcome does.
TEST(CrossCoverage, OnlyCountingBinsContributeToUserBinCount) {
  EXPECT_TRUE(
      CoverageDB::CrossBinCountsTowardCoverage(CrossSampleOutcome::kCounted));
  EXPECT_FALSE(
      CoverageDB::CrossBinCountsTowardCoverage(CrossSampleOutcome::kIgnored));
  EXPECT_FALSE(CoverageDB::CrossBinCountsTowardCoverage(
      CrossSampleOutcome::kIllegalError));
}

// LRM 19.11.2: the auto-cross bins built for a cross (the Cartesian product of
// the constituent coverpoints' bins, LRM 19.6) number exactly ∏ B_j, so the
// denominator the coverage uses agrees with CrossCoverageDenominator for a pure
// auto cross. A 2x2 cross has four bins.
TEST(CrossCoverage, AutoCreatedBinDenominatorMatchesFormula) {
  CoverageDB db;
  CoverGroup* g = nullptr;
  auto* xc = BuildTwoByTwoCross(db, g);

  // ∏ B_j = 2*2 = 4, matching the formula's denominator for a pure auto cross.
  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetCrossCoverage(xc, covered, total);
  EXPECT_EQ(static_cast<uint64_t>(total),
            CoverageDB::CrossCoverageDenominator({2, 2}, 0, 0));
  EXPECT_EQ(total, 4);
}

// LRM 19.11.2: cross coverage is |bins_covered| / (B_c + B_u). Covering two of
// the four bins of a 2x2 cross gives 50%.
TEST(CrossCoverage, CoverageIsCoveredOverDenominator) {
  CoverageDB db;
  CoverGroup* g = nullptr;
  auto* xc = BuildTwoByTwoCross(db, g);

  // Hit two of the four cross products.
  db.Sample(g, {{"a", 0}, {"b", 0}});
  db.Sample(g, {{"a", 1}, {"b", 1}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(xc), 50.0);
}

// LRM 19.11.2: a cross whose denominator B_c + B_u is zero is reported by
// CrossCoverageDenominatorZero. A cross with no bins has a zero denominator;
// one with a bin does not.
TEST(CrossCoverage, DenominatorZeroDetection) {
  CrossCover empty;
  empty.name = "empty";
  EXPECT_TRUE(CoverageDB::CrossCoverageDenominatorZero(&empty));

  CrossCover filled;
  filled.name = "filled";
  CrossBin bin;
  bin.name = "<0,0>";
  bin.value_sets = {{0}, {0}};
  filled.bins.push_back(bin);
  EXPECT_FALSE(CoverageDB::CrossCoverageDenominatorZero(&filled));
}

// LRM 19.11.2 b: when the cross denominator is zero and the cross weight is
// nonzero, get_coverage returns 0.0.
TEST(CrossCoverage, ZeroDenominatorNonzeroWeightReturnsZero) {
  CrossCover cross;
  cross.name = "x";
  cross.option.weight = 1;  // no bins: zero denominator
  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&cross), 0.0);
}

// LRM 19.11.2 c: when the cross denominator is zero and the cross weight is
// zero, get_coverage returns 100.0.
TEST(CrossCoverage, ZeroDenominatorZeroWeightReturns100) {
  CrossCover cross;
  cross.name = "x";
  cross.option.weight = 0;  // no bins: zero denominator
  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&cross), 100.0);
}

// LRM 19.11.2 d: the ref-int pair form on a zero-denominator cross reports zero
// for both the numerator and the denominator.
TEST(CrossCoverage, ZeroDenominatorTwoArgReportsZeroCounts) {
  CrossCover cross;
  cross.name = "x";

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetCrossCoverage(&cross, covered, total);
  EXPECT_EQ(covered, 0);
  EXPECT_EQ(total, 0);
}

// LRM 19.11.2 d: the ref-int pair form on a cross with a nonzero denominator
// reports the covered bins and the denominator B_c + B_u. With one of two cross
// bins covered, it reports 1 of 2.
TEST(CrossCoverage, TwoArgReportsCoveredAndDenominator) {
  CrossCover cross;
  cross.name = "x";
  CrossBin hit;
  hit.name = "<0,0>";
  hit.value_sets = {{0}, {0}};
  hit.hit_count = 1;
  cross.bins.push_back(hit);
  CrossBin miss;
  miss.name = "<1,1>";
  miss.value_sets = {{1}, {1}};
  cross.bins.push_back(miss);

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetCrossCoverage(&cross, covered, total);
  EXPECT_EQ(covered, 1);
  EXPECT_EQ(total, 2);
}

// LRM 19.11.2 (edge): when user-defined cross bins comprise every cross product
// (B_b == ∏ B_j), there are no auto-cross bins left, so B_c is zero and the
// denominator reduces to the significant user-defined bin count B_u alone.
TEST(CrossCoverage, AllProductsTakenByUserBinsLeaveNoAutoBins) {
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({3, 2}, 6), 0u);
  // Denominator is then purely B_u (here two user-defined cross bins).
  EXPECT_EQ(CoverageDB::CrossCoverageDenominator({3, 2}, 6, 2), 2u);
}

// LRM 19.11.2 (error): B_b is the number of cross products comprised by
// user-defined cross bins and can never exceed the total ∏ B_j. An ill-formed
// argument that does is clamped so the auto-cross bin count never underflows
// below zero.
TEST(CrossCoverage, UserProductsExceedingTotalClampToZero) {
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({3, 2}, 7), 0u);
}

// LRM 19.11.2 (edge): B_c is the product ∏ B_j over every crossed coverpoint,
// not just two. Crossing three coverpoints of two bins each gives 2*2*2 = 8.
TEST(CrossCoverage, ProductSpansAllCrossedCoverpoints) {
  EXPECT_EQ(CoverageDB::CrossAutoBinCount({2, 2, 2}, 0), 8u);
  EXPECT_EQ(CoverageDB::CrossCoverageDenominator({2, 2, 2}, 0, 0), 8u);
}

// LRM 19.11.2 (edge): the weight-dependent result applies only when the
// denominator is zero. A cross with bins present but none covered reports 0.0
// from the |covered|/(B_c+B_u) ratio even when its weight is zero — the
// zero-denominator zero-weight 100.0 rule does not apply here.
TEST(CrossCoverage, UncoveredCrossWithZeroWeightReportsZero) {
  CrossCover cross;
  cross.name = "x";
  cross.option.weight = 0;
  CrossBin b0;
  b0.name = "<0,0>";
  b0.value_sets = {{0}, {0}};
  cross.bins.push_back(b0);
  CrossBin b1;
  b1.name = "<1,1>";
  b1.value_sets = {{1}, {1}};
  cross.bins.push_back(b1);

  // Nothing covered: the denominator is nonzero (two bins) so coverage is 0/2,
  // not the zero-denominator zero-weight 100.0.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&cross), 0.0);
}

// LRM 19.11.2 a: a cross whose own denominator is zero does not contribute to
// the parent covergroup's coverage computation — it is dropped from both the
// numerator and the denominator of the covergroup average. With the empty cross
// dropped, the covergroup coverage is the surviving coverpoint's 100%, not a
// weighted average that the cross's 0.0 would pull down.
TEST(CrossCoverage, ZeroDenominatorCrossDroppedFromCovergroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* keep = CoverageDB::AddCoverPoint(g, "keep");
  CoverBin kb;
  kb.name = "b0";
  kb.values = {0};
  CoverageDB::AddBin(keep, kb);

  CrossCover empty;
  empty.name = "empty";
  empty.coverpoint_names = {"a", "b"};
  empty.option.weight = 1;  // no bins: zero denominator
  CoverageDB::AddCross(g, std::move(empty));

  db.Sample(g, {{"keep", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 100.0);
}

}  // namespace
