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

// LRM 19.5.2: a sequence of transitions "value1 => value3 => value4 => value5"
// may be of arbitrary length; the bin increments only when the sampled value
// stream completes the whole ordered sequence. Driven through Sample() so the
// runtime matching engine is what applies the rule.
TEST(CoverageTransitionBins, MultiStepSequenceIncrementsWhenCompleted) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "s";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = {{1, 3, 4, 5}};
  auto* b = CoverageDB::AddBin(cp, bin);

  // A leading value and then a broken run must not complete the sequence.
  db.Sample(g, {{"v", 1}});
  db.Sample(g, {{"v", 3}});
  db.Sample(g, {{"v", 9}});  // diverges from the expected 4
  EXPECT_EQ(b->hit_count, 0u);

  // The full ordered sequence increments on the sample that completes it.
  db.Sample(g, {{"v", 1}});
  db.Sample(g, {{"v", 3}});
  db.Sample(g, {{"v", 4}});
  EXPECT_EQ(b->hit_count, 0u);  // not yet complete
  db.Sample(g, {{"v", 5}});
  EXPECT_EQ(b->hit_count, 1u);
}

// LRM 19.5.2: a transition bin is incremented every time the coverpoint's value
// stream completes the bin's sequence, even when successive matches overlap. A
// consecutive repetition such as (5[*3]) matches once per sample once three 5's
// have been seen, so a run of six 5's produces four increments (mirrors bin b5
// of the LRM example). The bin's sequence is built with the production
// consecutive-repeat expansion helper.
TEST(CoverageTransitionBins, OverlappingConsecutiveMatchesEachIncrement) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "b5";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = CoverageDB::ExpandConsecutiveRepeat({5}, 3, 3);
  ASSERT_EQ(bin.transitions.size(), 1u);
  ASSERT_EQ(bin.transitions[0], (std::vector<int64_t>{5, 5, 5}));
  auto* b = CoverageDB::AddBin(cp, bin);

  for (int i = 0; i < 6; ++i) db.Sample(g, {{"v", 5}});
  EXPECT_EQ(b->hit_count, 4u);
}

// LRM 19.5.2: a set transition "range_list1 => range_list2" specifies a
// transition between each value of the first list and each of the second; when
// all of the expansions belong to one named bin, every distinct completion of
// any of them increments that single bin. The bin is populated from the
// production set-transition expansion helper and observed through Sample().
TEST(CoverageTransitionBins, SetTransitionProductDrivesSingleBin) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "sa";
  bin.kind = CoverBinKind::kTransition;
  // (1,5 => 6,7) expands to 1=>6, 1=>7, 5=>6, 5=>7.
  bin.transitions = CoverageDB::ExpandSetTransition({{1, 5}, {6, 7}});
  ASSERT_EQ(bin.transitions.size(), 4u);
  auto* b = CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 1}});
  db.Sample(g, {{"v", 6}});  // completes 1=>6
  EXPECT_EQ(b->hit_count, 1u);
  db.Sample(g, {{"v", 5}});
  db.Sample(g, {{"v", 7}});  // completes 5=>7
  EXPECT_EQ(b->hit_count, 2u);
}

// LRM 19.5.2: for a transition bin array declared as "binname[]", each element
// is a separate bin named "binname[transition]" and tracks its own bounded
// transition independently. Element bins are named with the production helper
// and driven through Sample(): only the element whose transition just completed
// increments.
TEST(CoverageTransitionBins, ArrayElementBinsTrackOwnTransition) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");

  auto expanded = CoverageDB::ExpandSetTransition({{1, 5}, {6, 7}});
  std::vector<CoverBin*> elems;
  for (const auto& seq : expanded) {
    CoverBin bin;
    bin.name = CoverageDB::TransitionArrayBinName("sb", seq);
    bin.kind = CoverBinKind::kTransition;
    bin.transitions = {seq};
    elems.push_back(CoverageDB::AddBin(cp, bin));
  }
  ASSERT_EQ(elems.size(), 4u);
  EXPECT_EQ(elems[0]->name, "sb[1=>6]");
  EXPECT_EQ(elems[3]->name, "sb[5=>7]");

  db.Sample(g, {{"v", 5}});
  db.Sample(g, {{"v", 7}});            // completes only the sb[5=>7] element
  EXPECT_EQ(elems[0]->hit_count, 0u);  // sb[1=>6]
  EXPECT_EQ(elems[1]->hit_count, 0u);  // sb[1=>7]
  EXPECT_EQ(elems[2]->hit_count, 0u);  // sb[5=>6]
  EXPECT_EQ(elems[3]->hit_count, 1u);  // sb[5=>7]
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

// LRM 19.5.2: a step of a set transition may be a value range rather than a
// single value, so a transition such as "[7:9],10 => 11,12" mixes a range and a
// value in its first step. The first step then carries the values 7,8,9,10 and
// the product is taken against the second step, yielding eight ordered
// transitions. Mirrors the second set of the LRM bin "sa".
TEST(CoverageTransitionBins, SetTransitionRangeStepExpandsToProduct) {
  auto seqs = CoverageDB::ExpandSetTransition({{7, 8, 9, 10}, {11, 12}});
  ASSERT_EQ(seqs.size(), 8u);
  EXPECT_EQ(seqs.front(), (std::vector<int64_t>{7, 11}));
  EXPECT_EQ(seqs.back(), (std::vector<int64_t>{10, 12}));

  // Drive one of the range-derived transitions through the runtime engine.
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "sa2";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = seqs;
  auto* b = CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 9}});
  db.Sample(g, {{"v", 11}});  // completes the range-derived 9=>11
  EXPECT_EQ(b->hit_count, 1u);
  db.Sample(g, {{"v", 10}});
  db.Sample(g, {{"v", 12}});  // completes 10=>12
  EXPECT_EQ(b->hit_count, 2u);
}

// LRM 19.5.2: a trans_list may hold more than one comma-separated set of
// transitions, all associated with the same named bin; a completed sequence
// from any of the sets increments that one bin. Mirrors the LRM bin
// "sa = (4=>5=>6), ([7:9],10=>11,12)".
TEST(CoverageTransitionBins, MultiSetTransListFeedsSingleBin) {
  auto set1 = CoverageDB::ExpandSetTransition({{4}, {5}, {6}});
  auto set2 = CoverageDB::ExpandSetTransition({{7, 8, 9, 10}, {11, 12}});
  ASSERT_EQ(set1.size(), 1u);
  ASSERT_EQ(set2.size(), 8u);

  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "sa";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = set1;
  bin.transitions.insert(bin.transitions.end(), set2.begin(), set2.end());
  auto* b = CoverageDB::AddBin(cp, bin);

  // A sequence from the first set increments the bin.
  db.Sample(g, {{"v", 4}});
  db.Sample(g, {{"v", 5}});
  db.Sample(g, {{"v", 6}});
  EXPECT_EQ(b->hit_count, 1u);

  // A sequence from the second set increments the same bin.
  db.Sample(g, {{"v", 8}});
  db.Sample(g, {{"v", 12}});
  EXPECT_EQ(b->hit_count, 2u);
}

// LRM 19.5.2: a length-0 transition specification is also illegal when its sole
// trans point is a value range, e.g. ([0:1]). The range denotes one sample
// point that can take either value, so it expands to the two single-point
// sequences {0} and {1}, each of length one and therefore an illegal
// transition.
TEST(CoverageTransitionBins, SingleRangeTransitionSpecIsIllegalLengthZero) {
  auto seqs = CoverageDB::ExpandSetTransition({{0, 1}});
  ASSERT_EQ(seqs.size(), 2u);
  for (const auto& seq : seqs) {
    EXPECT_EQ(seq.size(), 1u);
    EXPECT_FALSE(CoverageDB::TransitionLengthLegal(seq.size()));
  }
}

// LRM 19.5.2: a value range repeated exactly once, e.g. ([0:1][*1]), still
// describes a single sample point per alternative and so is an illegal length-0
// transition specification. Each value of the range, repeated once, yields a
// one-point sequence.
TEST(CoverageTransitionBins, RangeRepeatedOnceIsIllegalLengthZero) {
  for (int64_t value : {int64_t{0}, int64_t{1}}) {
    auto seqs = CoverageDB::ExpandConsecutiveRepeat({value}, 1, 1);
    ASSERT_EQ(seqs.size(), 1u);
    EXPECT_EQ(seqs[0], (std::vector<int64_t>{value}));
    EXPECT_FALSE(CoverageDB::TransitionLengthLegal(seqs[0].size()));
  }
}

// Builds a plain (single-occurrence) transition pattern element matching one
// value.
static TransitionPatternElement PatValue(int64_t value) {
  TransitionPatternElement e;
  e.values = {value};
  e.has_repeat = false;
  return e;
}

// Builds a repeated transition pattern element (goto or nonconsecutive).
static TransitionPatternElement PatRepeat(int64_t value, TransitionRepeatKind k,
                                          uint32_t lo, uint32_t hi) {
  TransitionPatternElement e;
  e.values = {value};
  e.has_repeat = true;
  e.repeat_kind = k;
  e.repeat_lo = lo;
  e.repeat_hi = hi;
  return e;
}

// LRM 19.5.2: a goto repetition "value [-> n]" matches when the value occurs
// the required number of times with any number of intervening samples between
// occurrences; the match completes at the last required occurrence. Driven
// through Sample() so the runtime matcher applies the rule.
TEST(CoverageTransitionBins, GotoRepetitionMatchesAcrossInterveningSamples) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "t";
  bin.kind = CoverBinKind::kTransition;
  // (3 [-> 2]): two 3's, gaps allowed between them.
  bin.transition_patterns = {{PatRepeat(3, TransitionRepeatKind::kGoto, 2, 2)}};
  auto* b = CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 3}});  // first occurrence
  EXPECT_EQ(b->hit_count, 0u);
  db.Sample(g, {{"v", 7}});  // intervening sample (not 3)
  db.Sample(g, {{"v", 4}});  // intervening sample (not 3)
  EXPECT_EQ(b->hit_count, 0u);
  db.Sample(g, {{"v", 3}});  // second occurrence completes the goto
  EXPECT_EQ(b->hit_count, 1u);
}

// LRM 19.5.2: the goto and nonconsecutive forms differ in what follows the last
// occurrence. With a goto, the following transition must immediately follow the
// last occurrence, so an intervening sample before it breaks the match; with a
// nonconsecutive repetition, later samples are tolerated before the following
// transition as long as the repetition value does not recur. The two bins see
// the identical stream 2,2,9,5 yet only the nonconsecutive one completes.
TEST(CoverageTransitionBins,
     GotoRequiresImmediateFollowNonconsecutiveTolerates) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* goto_cp = CoverageDB::AddCoverPoint(g, "vg");
  CoverBin goto_bin;
  goto_bin.name = "g";
  goto_bin.kind = CoverBinKind::kTransition;
  // (2 [-> 2] => 5): the 5 must immediately follow the second 2.
  goto_bin.transition_patterns = {
      {PatRepeat(2, TransitionRepeatKind::kGoto, 2, 2), PatValue(5)}};
  auto* gb = CoverageDB::AddBin(goto_cp, goto_bin);

  auto* nc_cp = CoverageDB::AddCoverPoint(g, "vn");
  CoverBin nc_bin;
  nc_bin.name = "n";
  nc_bin.kind = CoverBinKind::kTransition;
  // (2 [= 2] => 5): the 5 may follow later, as long as no further 2 occurs.
  nc_bin.transition_patterns = {
      {PatRepeat(2, TransitionRepeatKind::kNonconsecutive, 2, 2), PatValue(5)}};
  auto* nb = CoverageDB::AddBin(nc_cp, nc_bin);

  for (int64_t v : {int64_t{2}, int64_t{2}, int64_t{9}, int64_t{5}}) {
    db.Sample(g, {{"vg", v}, {"vn", v}});
  }
  // The intervening 9 breaks the goto (the 5 is no longer immediate) but is a
  // tolerated gap for the nonconsecutive form.
  EXPECT_EQ(gb->hit_count, 0u);
  EXPECT_EQ(nb->hit_count, 1u);
}

// LRM 19.5.2: reproduces the standard's worked transition-coverage example. A
// single coverpoint carries the bins b2=(2[->3:5]), b3=(3[->3:5]), b5=(5[*3]),
// b6=(1=>3[->4:6]=>1), and b7=(1=>2[=3:6]=>5). Driving the covergroup's sample
// stream through Sample() must reproduce the increment counts the standard
// states: b2 twice, b3 three times, b5 four times, and b6/b7 once each.
TEST(CoverageTransitionBins, WorkedExampleReproducesStandardBinCounts) {
  CoverageDB db;
  auto* g = db.CreateGroup("sg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");

  CoverBin b2;
  b2.name = "b2";
  b2.kind = CoverBinKind::kTransition;
  b2.transition_patterns = {{PatRepeat(2, TransitionRepeatKind::kGoto, 3, 5)}};
  auto* pb2 = CoverageDB::AddBin(cp, b2);

  CoverBin b3;
  b3.name = "b3";
  b3.kind = CoverBinKind::kTransition;
  b3.transition_patterns = {{PatRepeat(3, TransitionRepeatKind::kGoto, 3, 5)}};
  auto* pb3 = CoverageDB::AddBin(cp, b3);

  CoverBin b5;
  b5.name = "b5";
  b5.kind = CoverBinKind::kTransition;
  // Consecutive repetition is a determined-length sequence, so it is carried as
  // a concrete transition rather than a structured pattern.
  b5.transitions = CoverageDB::ExpandConsecutiveRepeat({5}, 3, 3);
  auto* pb5 = CoverageDB::AddBin(cp, b5);

  CoverBin b6;
  b6.name = "b6";
  b6.kind = CoverBinKind::kTransition;
  b6.transition_patterns = {{PatValue(1),
                             PatRepeat(3, TransitionRepeatKind::kGoto, 4, 6),
                             PatValue(1)}};
  auto* pb6 = CoverageDB::AddBin(cp, b6);

  CoverBin b7;
  b7.name = "b7";
  b7.kind = CoverBinKind::kTransition;
  b7.transition_patterns = {
      {PatValue(1), PatRepeat(2, TransitionRepeatKind::kNonconsecutive, 3, 6),
       PatValue(5)}};
  auto* pb7 = CoverageDB::AddBin(cp, b7);

  const std::vector<int64_t> stream = {1, 4, 3, 2, 3, 3, 2, 2, 3,
                                       2, 3, 1, 5, 5, 5, 5, 5, 5};
  for (int64_t v : stream) db.Sample(g, {{"v", v}});

  EXPECT_EQ(pb2->hit_count, 2u);
  EXPECT_EQ(pb3->hit_count, 3u);
  EXPECT_EQ(pb5->hit_count, 4u);
  EXPECT_EQ(pb6->hit_count, 1u);
  EXPECT_EQ(pb7->hit_count, 1u);
}

}  // namespace
