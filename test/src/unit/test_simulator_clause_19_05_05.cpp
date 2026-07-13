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
  remaining.reserve(distributed.size());
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

// --- Runtime observation of the exclusion rule through the real sample path --
// The tests above exercise the static removal/containment helpers in isolation.
// The following tests drive db.Sample() end to end so that the production
// scoring path (ScoreValueBins / ScoreTransitionBins / GetPointCoverage) is the
// code observed applying the rule, not just the helpers.

// The values of an ignore_bins state bin are excluded from coverage: a
// coverpoint carrying one ordinary bin and one ignore bin reports its coverage
// over the ordinary bin alone. The ignore bin never joins the coverage total —
// an uncovered ignore bin would otherwise drag coverage to 50%.
TEST(Coverage, IgnoreBinExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin good;
  good.name = "valid";
  good.values = {1};
  CoverageDB::AddBin(cp, good);

  CoverBin ign;
  ign.name = "ignore";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {7, 8};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"x", 1}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

// A sampled value that lands in an ignore bin is excluded from coverage at
// sample time: the ignore bin itself never records a hit even when its value
// occurs.
TEST(Coverage, IgnoredValueRecordsNoHitAtSampleTime) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin ign;
  ign.name = "ignore";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {7};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"x", 7}});

  EXPECT_EQ(cp->bins[0].hit_count, 0u);
}

// An ignored individual value has no effect on a transition that includes it:
// sampling through the ignored state value neither suppresses nor removes the
// legal transition passing through it, and the ignore bin records no hit. (This
// is the runtime counterpart of the always-false IgnoredValueAffectsTransition
// helper, observing the real ScoreValueBins / ScoreTransitionBins interaction.)
TEST(Coverage, IgnoredStateValueDoesNotSuppressTransitionThroughIt) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");

  // Legal transition bin 1=>2=>3=>4.
  CoverBin trans;
  trans.name = "seq";
  trans.kind = CoverBinKind::kTransition;
  trans.transitions = {{1, 2, 3, 4}};
  CoverageDB::AddBin(cp, trans);

  // Ignored state value 3, which the transition passes through.
  CoverBin ign;
  ign.name = "ign_state";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {3};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"s", 1}});
  db.Sample(g, {{"s", 2}});
  db.Sample(g, {{"s", 3}});  // ignored state value — no coverage effect
  db.Sample(g, {{"s", 4}});  // completes the legal transition

  // The ignored value had no effect on the transition that includes it: the
  // legal transition still hit, while the ignore bin recorded nothing.
  EXPECT_EQ(cp->bins[0].hit_count, 1u);
  EXPECT_EQ(cp->bins[1].hit_count, 0u);
}

// An ignored value is removed from the value set of any coverage bin, so a
// value that lands in both an ignore bin and an ordinary bin counts toward
// neither: the ordinary bin records no hit for the ignored value, while a
// non-ignored value it also lists still counts. (Observes the ignore-dominance
// applied by ScoreValueBins through the real sample path, not a helper.)
TEST(Coverage, IgnoredValueInAnotherBinIsNotCounted) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin ord;
  ord.name = "ordinary";
  ord.values = {5, 6};
  CoverageDB::AddBin(cp, ord);

  CoverBin ign;
  ign.name = "ignore";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {5};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"x", 5}});  // ignored — removed from the ordinary bin too
  EXPECT_EQ(cp->bins[0].hit_count, 0u);

  db.Sample(g, {{"x", 6}});  // not ignored — still counts for the ordinary bin
  EXPECT_EQ(cp->bins[0].hit_count, 1u);
}

// The transition form of ignore_bins is excluded from coverage just as the
// value-set form is: a coverpoint carrying one legal transition bin and one
// ignore transition bin reports coverage over the legal bin alone.
TEST(Coverage, IgnoreTransitionBinExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");

  CoverBin good;
  good.name = "good_trans";
  good.kind = CoverBinKind::kTransition;
  good.transitions = {{1, 2}};
  CoverageDB::AddBin(cp, good);

  CoverBin ign;
  ign.name = "ign_trans";
  ign.kind = CoverBinKind::kIgnore;
  ign.transitions = {{7, 8}};
  CoverageDB::AddBin(cp, ign);

  // Complete only the legal transition; the ignored transition never occurs.
  db.Sample(g, {{"s", 1}});
  db.Sample(g, {{"s", 2}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

}  // namespace
