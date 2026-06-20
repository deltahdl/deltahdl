#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, WildcardBinMatchesValues) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "data");
  CoverBin wbin;
  wbin.name = "w_even";
  wbin.kind = CoverBinKind::kWildcard;
  wbin.values = {0, 2, 4, 6};
  CoverageDB::AddBin(cp, wbin);

  db.Sample(g, {{"data", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);

  db.Sample(g, {{"data", 3}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

// --- LRM 19.5.5: excluding coverage point values or transitions -------------

// Each value named by an ignore_bins state set is removed from a coverage bin's
// value set; values not ignored stay, and duplicates of an ignored value are
// all dropped.
TEST(Coverage, IgnoredValuesRemovedFromStateBin) {
  std::vector<int64_t> bin_values = {5, 7, 8, 7, 9};
  std::vector<int64_t> ignored = {7, 8};
  EXPECT_EQ(CoverageDB::RemoveIgnoredValues(bin_values, ignored),
            (std::vector<int64_t>{5, 9}));

  // Ignoring values absent from the bin leaves it unchanged.
  EXPECT_EQ(CoverageDB::RemoveIgnoredValues({1, 2, 3}, {4}),
            (std::vector<int64_t>{1, 2, 3}));
}

// The removal happens after distribution: distributing first and then removing
// the ignored values yields the same per-bin contents as the LRM requires.
TEST(Coverage, IgnoredValuesRemovedAfterDistribution) {
  std::vector<int64_t> values = {1, 2, 3, 4, 5, 6};
  auto distributed = CoverageDB::DistributeValues(values, 3);
  std::vector<int64_t> ignored = {3, 4};
  std::vector<std::vector<int64_t>> remaining;
  for (const auto& bin : distributed) {
    remaining.push_back(CoverageDB::RemoveIgnoredValues(bin, ignored));
  }
  EXPECT_EQ(remaining, (std::vector<std::vector<int64_t>>{{1, 2}, {}, {5, 6}}));
}

// A covered transition is removed when it cannot occur without also matching an
// ignored sequence, i.e. when the ignored sequence is a contiguous subsequence
// of the covered one (ignoring 2=>3 removes 1=>2=>3=>4).
TEST(Coverage, CoveredTransitionRemovedWhenContainsIgnored) {
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIgnored({1, 2, 3, 4}, {2, 3}));
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIgnored({2, 3}, {2, 3}));
  // A non-contiguous occurrence does not trigger removal.
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIgnored({2, 9, 3}, {2, 3}));
  // An unrelated ignored sequence leaves the covered transition in place.
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIgnored({1, 2, 3, 4}, {5, 6}));
}

// An ignored individual value has no effect on a transition that includes the
// value: the transition bin is not removed merely because it passes through it.
TEST(Coverage, IgnoredValueDoesNotAffectTransition) {
  EXPECT_FALSE(CoverageDB::IgnoredValueAffectsTransition(3, {1, 2, 3, 4}));
  EXPECT_FALSE(CoverageDB::IgnoredValueAffectsTransition(7, {7, 7}));
}

// An ignore_bins transition cannot specify a sequence of unbounded or
// undetermined varying length; only a bounded sequence is legal. The bounded
// classification comes from the §19.5.2 repetition machinery.
TEST(Coverage, IgnoreTransitionMustBeBounded) {
  EXPECT_TRUE(CoverageDB::IgnoreTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kConsecutive)));
  EXPECT_FALSE(CoverageDB::IgnoreTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kGoto)));
  EXPECT_FALSE(CoverageDB::IgnoreTransitionLengthLegal(
      CoverageDB::TransitionRepeatBounded(
          TransitionRepeatKind::kNonconsecutive)));
}

// Edge case for the state removal rule: when every value of a bin is ignored,
// the bin is left with no values at all. This is the precondition for the
// empty-bin exclusion handled by §19.11.
TEST(Coverage, IgnoringEveryValueEmptiesStateBin) {
  EXPECT_TRUE(CoverageDB::RemoveIgnoredValues({1, 2, 3}, {3, 1, 2}).empty());
  // An empty bin stays empty regardless of what is ignored.
  EXPECT_TRUE(CoverageDB::RemoveIgnoredValues({}, {5}).empty());
}

// Edge case for the state removal rule: an empty ignore set removes nothing, so
// the bin keeps all of its values in order.
TEST(Coverage, EmptyIgnoreSetLeavesStateBinUnchanged) {
  EXPECT_EQ(CoverageDB::RemoveIgnoredValues({4, 2, 4, 6}, {}),
            (std::vector<int64_t>{4, 2, 4, 6}));
}

// Edge case for the transition removal rule: an ignored sequence longer than a
// covered sequence cannot be contained in it, so the covered sequence stays.
TEST(Coverage, LongerIgnoredSequenceDoesNotRemoveTransition) {
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIgnored({2, 3}, {1, 2, 3, 4}));
}

// Edge case for the transition removal rule: an empty ignored sequence matches
// nothing and never removes a covered transition.
TEST(Coverage, EmptyIgnoredSequenceDoesNotRemoveTransition) {
  EXPECT_FALSE(CoverageDB::CoveredTransitionIsIgnored({1, 2, 3}, {}));
}

// Edge case for the transition removal rule: containment is recognized at the
// very start and the very end of the covered sequence, not only in its middle.
TEST(Coverage, IgnoredSequenceMatchedAtTransitionBoundaries) {
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIgnored({2, 3, 4}, {2, 3}));
  EXPECT_TRUE(CoverageDB::CoveredTransitionIsIgnored({1, 2, 3}, {2, 3}));
}

}  // namespace
