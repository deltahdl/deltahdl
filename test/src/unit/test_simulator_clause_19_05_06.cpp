#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, IllegalBinsExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin good;
  good.name = "valid";
  good.values = {1};
  CoverageDB::AddBin(cp, good);

  CoverBin bad;
  bad.name = "illegal";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {0xFF};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"x", 1}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

// --- LRM 19.5.6: illegal coverage point values or transitions ---------------

// For state bins, each illegal value is removed from the set of values
// associated with any coverage bin; every occurrence is dropped and the rest
// keep their order. Removing values absent from the bin leaves it unchanged.
TEST(Coverage, IllegalValuesRemovedFromStateBin) {
  EXPECT_EQ(CoverageDB::RemoveIllegalValues({5, 7, 8, 7, 9}, {7, 8}),
            (std::vector<int64_t>{5, 9}));
  EXPECT_EQ(CoverageDB::RemoveIllegalValues({1, 2, 3}, {4}),
            (std::vector<int64_t>{1, 2, 3}));
}

// The removal of illegal values occurs after the distribution of values to the
// specified bins: distributing first and then removing yields the per-bin
// contents the LRM requires.
TEST(Coverage, IllegalValuesRemovedAfterDistribution) {
  auto distributed = CoverageDB::DistributeValues({1, 2, 3, 4, 5, 6}, 3);
  std::vector<int64_t> illegal = {3, 4};
  std::vector<std::vector<int64_t>> remaining;
  remaining.reserve(distributed.size());
  for (const auto& bin : distributed) {
    remaining.push_back(CoverageDB::RemoveIllegalValues(bin, illegal));
  }
  EXPECT_EQ(remaining, (std::vector<std::vector<int64_t>>{{1, 2}, {}, {5, 6}}));
}

// Removing every value of a bin leaves it empty — the precondition for the
// empty-bin exclusion handled by 19.11.
TEST(Coverage, IllegalRemovalCanEmptyStateBin) {
  EXPECT_TRUE(CoverageDB::RemoveIllegalValues({1, 2, 3}, {3, 1, 2}).empty());
}

// Edge case: an empty illegal set removes nothing, so the bin keeps all of its
// values in their original order.
TEST(Coverage, EmptyIllegalSetLeavesStateBinUnchanged) {
  EXPECT_EQ(CoverageDB::RemoveIllegalValues({4, 2, 4, 6}, {}),
            (std::vector<int64_t>{4, 2, 4, 6}));
}

// A covered transition is removed when it cannot occur without also matching an
// illegal sequence, i.e. when the illegal sequence is a contiguous subsequence
// of the covered one (an illegal 2=>3 removes the covered 1=>2=>3=>4).
TEST(Coverage, CoveredTransitionRemovedWhenContainsIllegal) {
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIllegal({1, 2, 3, 4}, {2, 3}));
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIllegal({2, 3, 4}, {2, 3}));
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIllegal({1, 2, 3}, {2, 3}));
  // Boundary: the illegal sequence may be the whole covered sequence.
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIllegal({2, 3}, {2, 3}));
  // Non-contiguous occurrence, unrelated sequence, longer illegal sequence, and
  // an empty illegal sequence never remove the covered transition.
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIllegal({2, 9, 3}, {2, 3}));
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIllegal({1, 2, 3, 4}, {5, 6}));
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIllegal({2, 3}, {1, 2, 3, 4}));
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIllegal({1, 2, 3}, {}));
}

// Specifying an illegal individual value has no effect on a transition that
// includes the value.
TEST(Coverage, IllegalValueDoesNotAffectTransition) {
  EXPECT_FALSE(CoverageDB::IllegalValueAffectsTransition(3, {1, 2, 3, 4}));
  EXPECT_FALSE(CoverageDB::IllegalValueAffectsTransition(7, {7, 7}));
}

// An illegal_bins transition cannot specify a sequence of unbounded or
// undetermined varying length; only a bounded sequence is legal. The bounded
// classification comes from the 19.5.2 repetition machinery.
TEST(Coverage, IllegalTransitionMustBeBounded) {
  EXPECT_TRUE(CoverageDB::IllegalTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kConsecutive)));
  EXPECT_FALSE(CoverageDB::IllegalTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kGoto)));
  EXPECT_FALSE(CoverageDB::IllegalTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(
          TransitionRepeatKind::kNonconsecutive)));
}

// Illegal bins take precedence over any other bins: an illegal hit raises a
// run-time error whether or not the value is also included in another bin.
TEST(Coverage, IllegalTakesPrecedenceOverOtherBins) {
  EXPECT_TRUE(CoverageDB::IllegalTakesPrecedence(true));
  EXPECT_TRUE(CoverageDB::IllegalTakesPrecedence(false));
}

// When an illegal value occurs during sampling, a run-time error is issued and
// the illegal bin itself records no hit.
TEST(Coverage, IllegalValueOccurrenceIssuesRuntimeError) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  CoverBin ib;
  ib.name = "bad";
  ib.kind = CoverBinKind::kIllegal;
  ib.values = {0xFF};
  CoverageDB::AddBin(cp, ib);

  db.Sample(g, {{"addr", 0xFF}});

  EXPECT_EQ(cp->illegal_violations, 1u);
  EXPECT_EQ(cp->bins[0].hit_count, 0u);
}

// A sampled value that hits no illegal bin raises no run-time error: the
// illegal-occurrence path fires only for an actual illegal hit.
TEST(Coverage, LegalValueRaisesNoIllegalViolation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin legal;
  legal.name = "legal";
  legal.values = {1};
  CoverageDB::AddBin(cp, legal);
  CoverBin bad;
  bad.name = "bad";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {0xFF};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"x", 1}});

  EXPECT_EQ(cp->illegal_violations, 0u);
  EXPECT_EQ(cp->bins[0].hit_count, 1u);
}

// Illegal precedence in effect: a value that lies in both an illegal bin and a
// legal bin raises the run-time error and is counted toward no coverage bin.
TEST(Coverage, IllegalValueInAnotherBinStillErrorsAndIsNotCounted) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin legal;
  legal.name = "legal";
  legal.values = {7};
  CoverageDB::AddBin(cp, legal);
  CoverBin bad;
  bad.name = "bad";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {7};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"x", 7}});

  EXPECT_EQ(cp->illegal_violations, 1u);
  EXPECT_EQ(cp->bins[0].hit_count, 0u);
}

// When an illegal transition sequence completes during sampling, a run-time
// error is issued; the illegal transition bin records no hit.
TEST(Coverage, IllegalTransitionOccurrenceIssuesRuntimeError) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");
  CoverBin bad;
  bad.name = "bad_trans";
  bad.kind = CoverBinKind::kIllegal;
  bad.transitions = {{4, 5, 6}};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"s", 4}});
  db.Sample(g, {{"s", 5}});
  db.Sample(g, {{"s", 6}});

  EXPECT_EQ(cp->illegal_violations, 1u);
  EXPECT_EQ(cp->bins[0].hit_count, 0u);
}

}  // namespace
