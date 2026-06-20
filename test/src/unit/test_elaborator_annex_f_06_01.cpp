#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_extended_booleans.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "helpers_annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

// §F.6.1 (triggered): with no local variables, T(V).triggered holds at j iff
// some subword ending at j tightly satisfies T. A two-letter sequence a ##1 b
// ending at j=1 is triggered there, with the empty context flowing through.
TEST(ExtendedBooleans, TriggeredHoldsWhenASubwordEndingAtJMatches) {
  auto seq = SeqConcat(Bool("a"), Bool("b"));
  const Word word{A({"a"}), A({"b"})};
  EXPECT_TRUE(SameContexts(
      TriggeredOutputs(word, /*j=*/1, *seq, NameSet{}, LocalContext{}),
      {LocalContext{}}));
  EXPECT_TRUE(TriggeredSatisfies(word, /*j=*/1, *seq, NameSet{}, LocalContext{},
                                 LocalContext{}));
}

// §F.6.1 (triggered): the start point i is existential -- triggered looks for
// any 0 <= i <= j whose subword w^{i,j} matches. A single Boolean is triggered
// only at the point it holds, not earlier.
TEST(ExtendedBooleans, TriggeredSearchesEveryStartPoint) {
  auto seq = Bool("a");
  const Word word{A({}), A({"a"})};
  // Ends at j=1 with the start point i=1; the empty leading letter is skipped.
  EXPECT_TRUE(TriggeredSatisfies(word, /*j=*/1, *seq, NameSet{}, LocalContext{},
                                 LocalContext{}));
  // No subword ending at j=0 satisfies a, since w^0 does not.
  EXPECT_TRUE(
      TriggeredOutputs(word, /*j=*/0, *seq, NameSet{}, LocalContext{}).empty());
}

// §F.6.1 (triggered): L_1 = L_0|_D U L|_V. A name sampled by T that is not
// among the actual arguments V does not flow out, while an unrelated incoming
// name in L_0 is preserved.
TEST(ExtendedBooleans, TriggeredDropsLocalsNotPassedAsActuals) {
  auto seq = Samp("v");
  const Word word{A({"x"})};
  const LocalContext input{{"u", A({"z"})}};
  // V = {}: the sampled v is discarded; the incoming u survives.
  EXPECT_TRUE(SameContexts(
      TriggeredOutputs(word, /*j=*/0, *seq, NameSet{}, input), {input}));
}

// §F.6.1 (triggered): a name in the actual arguments V flows back out, carrying
// the value the body sampled, alongside the preserved incoming names.
TEST(ExtendedBooleans, TriggeredFlowsActualArgumentsBackOut) {
  auto seq = Samp("v");
  const Word word{A({"x"})};
  const LocalContext input{{"u", A({"z"})}};
  // V = {v}: v escapes bound to the observed letter; u is still kept.
  EXPECT_TRUE(
      SameContexts(TriggeredOutputs(word, /*j=*/0, *seq, NameSet{"v"}, input),
                   {LocalContext{{"u", A({"z"})}, {"v", A({"x"})}}}));
}

// §F.6.1 (triggered): D = dom(L_0) - (dom(L) & V) drops an incoming binding the
// call overwrites, so the freshly sampled value replaces the old one rather
// than colliding with it.
TEST(ExtendedBooleans, TriggeredOverwritesIncomingNameAlsoSampled) {
  auto seq = Samp("v");
  const Word word{A({"x"})};
  const LocalContext input{{"v", A({"old"})}};
  // v is both incoming and sampled, and passed as an actual: D excludes v, so
  // only the new binding remains.
  EXPECT_TRUE(
      SameContexts(TriggeredOutputs(word, /*j=*/0, *seq, NameSet{"v"}, input),
                   {LocalContext{{"v", A({"x"})}}}));
}

// §F.6.1 (triggered): a sampled name overwritten by the body but NOT passed
// back (v not in V) leaves the incoming binding of v in place, because v stays
// in D.
TEST(ExtendedBooleans, TriggeredKeepsIncomingNameWhenNotAnActual) {
  auto seq = Samp("v");
  const Word word{A({"x"})};
  const LocalContext input{{"v", A({"old"})}};
  // V = {}: dom(L) & V is empty, so D keeps v and the incoming value survives.
  EXPECT_TRUE(
      SameContexts(TriggeredOutputs(word, /*j=*/0, *seq, NameSet{}, input),
                   {LocalContext{{"v", A({"old"})}}}));
}

// §F.6.1 (triggered) boundary: j must lie in 0 <= j < |w|; a point at or past
// the end of the word yields no output context.
TEST(ExtendedBooleans, TriggeredRejectsOutOfRangePoint) {
  auto seq = Bool("a");
  const Word word{A({"a"})};
  EXPECT_TRUE(
      TriggeredOutputs(word, /*j=*/1, *seq, NameSet{}, LocalContext{}).empty());
}

// §F.6.1 (matched): @(c)(T(V).matched) holds at j when T is triggered at an
// earlier point i and the destination clock c ticks exactly once, at j. Here a
// triggers at i=0 and clk ticks once at j=2.
TEST(ExtendedBooleans, MatchedHoldsWhenClockTicksOnceAfterTrigger) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  const Word word{A({"a"}), A({}), A({"clk"})};
  EXPECT_TRUE(MatchedSatisfies(word, /*j=*/2, *seq, NameSet{}, clk,
                               LocalContext{}, LocalContext{}));
}

// §F.6.1 (matched): the gap w^{i+1,j} must satisfy c[->1], so the clock may not
// tick before j. A clock edge inside the gap leaves matched unsatisfied.
TEST(ExtendedBooleans, MatchedRejectsClockTickBeforeJ) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  // a triggers at i=0, but clk ticks at point 1, before j=2.
  const Word word{A({"a"}), A({"clk"}), A({"clk"})};
  EXPECT_TRUE(
      MatchedOutputs(word, /*j=*/2, *seq, NameSet{}, clk, LocalContext{})
          .empty());
}

// §F.6.1 (matched): the trigger point i is strictly earlier than j (0 <= i <
// j), so matched can never hold at j=0.
TEST(ExtendedBooleans, MatchedRequiresAStrictlyEarlierTrigger) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  const Word word{A({"a"})};
  EXPECT_TRUE(
      MatchedOutputs(word, /*j=*/0, *seq, NameSet{}, clk, LocalContext{})
          .empty());
}

// §F.6.1 (matched): the immediate case, where the trigger point is j-1 and the
// gap w^{i+1,j} is the single letter w^j, requires the clock to hold at j.
TEST(ExtendedBooleans, MatchedAllowsAdjacentTriggerAndTick) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  // a triggers at i=0; the gap is the single letter w^1, which carries clk.
  const Word word{A({"a"}), A({"clk"})};
  EXPECT_TRUE(MatchedSatisfies(word, /*j=*/1, *seq, NameSet{}, clk,
                               LocalContext{}, LocalContext{}));
}

// §F.6.1 (matched): the output context of matched is exactly the one triggered
// produced at i; the clock gap carries no local variables. A name passed back
// through V at the trigger point flows out of matched too.
TEST(ExtendedBooleans, MatchedCarriesTheTriggeredOutputContext) {
  auto seq = Samp("v");
  auto clk = BoolAtom("clk");
  // v is sampled at i=0; clk ticks once at j=1.
  const Word word{A({"x"}), A({"clk"})};
  EXPECT_TRUE(SameContexts(
      MatchedOutputs(word, /*j=*/1, *seq, NameSet{"v"}, clk, LocalContext{}),
      {LocalContext{{"v", A({"x"})}}}));
  // Without v among the actuals the sampled value does not escape.
  EXPECT_TRUE(SameContexts(
      MatchedOutputs(word, /*j=*/1, *seq, NameSet{}, clk, LocalContext{}),
      {LocalContext{}}));
}

// §F.6.1 (triggered) error condition: L_1 is determined by the rule, so the
// four-way predicate accepts only the yielded output context and rejects any
// other -- a wrong value bound to v, or a context that drops v entirely.
TEST(ExtendedBooleans, TriggeredPredicateRejectsWrongOutputContext) {
  auto seq = Samp("v");
  const Word word{A({"x"})};
  EXPECT_TRUE(TriggeredSatisfies(word, /*j=*/0, *seq, NameSet{"v"},
                                 LocalContext{},
                                 LocalContext{{"v", A({"x"})}}));
  EXPECT_FALSE(TriggeredSatisfies(word, /*j=*/0, *seq, NameSet{"v"},
                                  LocalContext{},
                                  LocalContext{{"v", A({"y"})}}));
  EXPECT_FALSE(TriggeredSatisfies(word, /*j=*/0, *seq, NameSet{"v"},
                                  LocalContext{}, LocalContext{}));
}

// §F.6.1 (matched) boundary: matched also requires 0 <= j < |w|; a point at or
// past the end of the word yields no output context.
TEST(ExtendedBooleans, MatchedRejectsOutOfRangePoint) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  const Word word{A({"a"}), A({"clk"})};
  EXPECT_TRUE(
      MatchedOutputs(word, /*j=*/2, *seq, NameSet{}, clk, LocalContext{})
          .empty());
}

// §F.6.1 (matched) error condition: both conjuncts are required. Here the clock
// c[->1] is satisfied over the gap, but T(V) is not triggered at the matching
// point i, so matched does not hold even though the clock ticks once at j.
TEST(ExtendedBooleans, MatchedRequiresTriggerNotJustClock) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  // clk ticks once at j=1, but a never triggers at i=0 (w^0 lacks a).
  const Word word{A({}), A({"clk"})};
  EXPECT_TRUE(
      MatchedOutputs(word, /*j=*/1, *seq, NameSet{}, clk, LocalContext{})
          .empty());
}

}  // namespace
