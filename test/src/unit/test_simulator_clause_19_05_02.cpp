#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// LRM 19.5.2: transition bins of a real coverpoint are not allowed.
TEST(CoverageTransitionBins, TransitionBinRejectedForRealCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* integral = CoverageDB::AddCoverPoint(g, "v");
  auto* real_cp = CoverageDB::AddCoverPoint(g, "r");
  real_cp->is_real = true;

  EXPECT_TRUE(CoverageDB::TransitionBinAllowed(integral));
  EXPECT_FALSE(CoverageDB::TransitionBinAllowed(real_cp));
}

// LRM 19.5.2: a length-0 transition specification (a single sample point) is
// illegal; a valid transition spans at least two points.
TEST(CoverageTransitionBins, LengthZeroTransitionIllegal) {
  EXPECT_FALSE(CoverageDB::TransitionLengthLegal(0));
  EXPECT_FALSE(CoverageDB::TransitionLengthLegal(1));
  EXPECT_TRUE(CoverageDB::TransitionLengthLegal(2));
  EXPECT_TRUE(CoverageDB::TransitionLengthLegal(5));
}

// LRM 19.5.2: a set transition "range_list1 => range_list2" expands to a
// transition between each value of the first list and each of the second.
TEST(CoverageTransitionBins, SetTransitionExpandsToProduct) {
  auto seqs = CoverageDB::ExpandSetTransition({{1, 5}, {6, 7}});
  ASSERT_EQ(seqs.size(), 4u);
  EXPECT_EQ(seqs[0], (std::vector<int64_t>{1, 6}));
  EXPECT_EQ(seqs[1], (std::vector<int64_t>{1, 7}));
  EXPECT_EQ(seqs[2], (std::vector<int64_t>{5, 6}));
  EXPECT_EQ(seqs[3], (std::vector<int64_t>{5, 7}));
}

// LRM 19.5.2: a single-value chain still expands through every step.
TEST(CoverageTransitionBins, SetTransitionThreeSteps) {
  auto seqs = CoverageDB::ExpandSetTransition({{1}, {3}, {5}});
  ASSERT_EQ(seqs.size(), 1u);
  EXPECT_EQ(seqs[0], (std::vector<int64_t>{1, 3, 5}));
}

// LRM 19.5.2: "item [* n]" repeats the item n times, e.g. 3[*5] is
// 3=>3=>3=>3=>3.
TEST(CoverageTransitionBins, ConsecutiveRepeatFixedCount) {
  auto seqs = CoverageDB::ExpandConsecutiveRepeat({3}, 5, 5);
  ASSERT_EQ(seqs.size(), 1u);
  EXPECT_EQ(seqs[0], (std::vector<int64_t>{3, 3, 3, 3, 3}));
}

// LRM 19.5.2: "item [* lo:hi]" yields one sequence per count in [lo, hi].
TEST(CoverageTransitionBins, ConsecutiveRepeatRange) {
  auto seqs = CoverageDB::ExpandConsecutiveRepeat({3}, 3, 5);
  ASSERT_EQ(seqs.size(), 3u);
  EXPECT_EQ(seqs[0], (std::vector<int64_t>{3, 3, 3}));
  EXPECT_EQ(seqs[1], (std::vector<int64_t>{3, 3, 3, 3}));
  EXPECT_EQ(seqs[2], (std::vector<int64_t>{3, 3, 3, 3, 3}));
}

// LRM 19.5.2: a transition bin array element is named by the bounded
// transition it matched, e.g. "sb[4=>5=>6]".
TEST(CoverageTransitionBins, ArrayBinNamesEmbedTransition) {
  EXPECT_EQ(CoverageDB::TransitionArrayBinName("sb", {4, 5, 6}), "sb[4=>5=>6]");
  EXPECT_EQ(CoverageDB::TransitionArrayBinName("sb", {10, 12}), "sb[10=>12]");
}

// LRM 19.5.2: consecutive repetition is bounded; goto and nonconsecutive are
// not, and so cannot be used with the multiple bins "[]" construct.
TEST(CoverageTransitionBins, UnboundedRepeatRejectedForMultipleBins) {
  EXPECT_TRUE(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kConsecutive));
  EXPECT_FALSE(
      CoverageDB::TransitionRepeatBounded(TransitionRepeatKind::kGoto));
  EXPECT_FALSE(CoverageDB::TransitionRepeatBounded(
      TransitionRepeatKind::kNonconsecutive));

  EXPECT_TRUE(
      CoverageDB::MultipleBinsAllowsTransition(/*sequence_bounded=*/true));
  EXPECT_FALSE(
      CoverageDB::MultipleBinsAllowsTransition(/*sequence_bounded=*/false));
}

// LRM 19.5.2: a default sequence specification does not accept the "[]"
// notation.
TEST(CoverageTransitionBins, DefaultSequenceRejectsMultipleBins) {
  EXPECT_FALSE(CoverageDB::DefaultSequenceAllowsMultipleBins());
}

// LRM 19.5.2: the default sequence bin counts only when no other transition
// bin fired this sample and nothing is still pending.
TEST(CoverageTransitionBins, DefaultSequenceIncrementCondition) {
  EXPECT_TRUE(CoverageDB::DefaultSequenceTransitionIncrements(
      /*any_nondefault_incremented=*/false, /*any_pending=*/false));
  EXPECT_FALSE(CoverageDB::DefaultSequenceTransitionIncrements(
      /*any_nondefault_incremented=*/true, /*any_pending=*/false));
  EXPECT_FALSE(CoverageDB::DefaultSequenceTransitionIncrements(
      /*any_nondefault_incremented=*/false, /*any_pending=*/true));
}

// LRM 19.5.2: a transition bin is incremented at most once per sample, even
// when more than one of its sequences would complete on that sample.
TEST(CoverageTransitionBins, TransitionBinCountsAtMostOncePerSample) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "t";
  bin.kind = CoverBinKind::kTransition;
  // Two sequences that both complete on the 1=>2 transition.
  bin.transitions = {{1, 2}, {1, 2}};
  auto* b = CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 1}});
  db.Sample(g, {{"v", 2}});
  EXPECT_EQ(b->hit_count, 1u);

  // A second 1=>2 transition increments the bin once more.
  db.Sample(g, {{"v", 1}});
  db.Sample(g, {{"v", 2}});
  EXPECT_EQ(b->hit_count, 2u);
}

// LRM 19.5.2 (edge): a set transition with no steps denotes no transition at
// all and expands to nothing.
TEST(CoverageTransitionBins, SetTransitionWithNoStepsYieldsNothing) {
  auto seqs = CoverageDB::ExpandSetTransition({});
  EXPECT_TRUE(seqs.empty());
}

// LRM 19.5.2 (error): a repeat range whose high bound is below its low bound
// describes no repetition count and expands to nothing.
TEST(CoverageTransitionBins, ConsecutiveRepeatInvertedRangeYieldsNothing) {
  auto seqs = CoverageDB::ExpandConsecutiveRepeat({3}, 5, 3);
  EXPECT_TRUE(seqs.empty());
}

// LRM 19.5.2 (edge): a single value range repeated exactly once, e.g. (0[*1]),
// expands to one sample point and is therefore an illegal length-0 transition
// specification.
TEST(CoverageTransitionBins, RepeatOnceProducesIllegalLengthZeroSpec) {
  auto seqs = CoverageDB::ExpandConsecutiveRepeat({0}, 1, 1);
  ASSERT_EQ(seqs.size(), 1u);
  EXPECT_EQ(seqs[0], (std::vector<int64_t>{0}));
  EXPECT_FALSE(CoverageDB::TransitionLengthLegal(seqs[0].size()));
}

}  // namespace
