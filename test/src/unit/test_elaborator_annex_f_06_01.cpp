#include <gtest/gtest.h>

#include <optional>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_extended_booleans.h"
#include "elaborator/annex_f_extended_expressions.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "helpers_annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

TEST(ExtendedBooleans, TriggeredHoldsWhenASubwordEndingAtJMatches) {
  auto seq = SeqConcat(Bool("a"), Bool("b"));
  const Word kWord{A({"a"}), A({"b"})};
  EXPECT_TRUE(SameContexts(
      TriggeredOutputs({kWord, 1, *seq, NameSet{}}, LocalContext{}),
      {LocalContext{}}));
  EXPECT_TRUE(TriggeredSatisfies({kWord, 1, *seq, NameSet{}}, LocalContext{},
                                 LocalContext{}));
}

TEST(ExtendedBooleans, TriggeredSearchesEveryStartPoint) {
  auto seq = Bool("a");
  const Word kWord{A({}), A({"a"})};
  EXPECT_TRUE(TriggeredSatisfies({kWord, 1, *seq, NameSet{}}, LocalContext{},
                                 LocalContext{}));
  EXPECT_TRUE(
      TriggeredOutputs({kWord, 0, *seq, NameSet{}}, LocalContext{}).empty());
}

TEST(ExtendedBooleans, TriggeredDropsLocalsNotPassedAsActuals) {
  auto seq = Samp("v");
  const Word kWord{A({"x"})};
  const LocalContext kInput{{"u", A({"z"})}};
  EXPECT_TRUE(SameContexts(
      TriggeredOutputs({kWord, 0, *seq, NameSet{}}, kInput), {kInput}));
}

TEST(ExtendedBooleans, TriggeredFlowsActualArgumentsBackOut) {
  auto seq = Samp("v");
  const Word kWord{A({"x"})};
  const LocalContext kInput{{"u", A({"z"})}};
  EXPECT_TRUE(
      SameContexts(TriggeredOutputs({kWord, 0, *seq, NameSet{"v"}}, kInput),
                   {LocalContext{{"u", A({"z"})}, {"v", A({"x"})}}}));
}

TEST(ExtendedBooleans, TriggeredOverwritesIncomingNameAlsoSampled) {
  auto seq = Samp("v");
  const Word kWord{A({"x"})};
  const LocalContext kInput{{"v", A({"old"})}};
  EXPECT_TRUE(
      SameContexts(TriggeredOutputs({kWord, 0, *seq, NameSet{"v"}}, kInput),
                   {LocalContext{{"v", A({"x"})}}}));
}

TEST(ExtendedBooleans, TriggeredKeepsIncomingNameWhenNotAnActual) {
  auto seq = Samp("v");
  const Word kWord{A({"x"})};
  const LocalContext kInput{{"v", A({"old"})}};
  EXPECT_TRUE(
      SameContexts(TriggeredOutputs({kWord, 0, *seq, NameSet{}}, kInput),
                   {LocalContext{{"v", A({"old"})}}}));
}

TEST(ExtendedBooleans, TriggeredRejectsOutOfRangePoint) {
  auto seq = Bool("a");
  const Word kWord{A({"a"})};
  EXPECT_TRUE(
      TriggeredOutputs({kWord, 1, *seq, NameSet{}}, LocalContext{}).empty());
}

TEST(ExtendedBooleans, MatchedHoldsWhenClockTicksOnceAfterTrigger) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  const Word kWord{A({"a"}), A({}), A({"clk"})};
  EXPECT_TRUE(MatchedSatisfies({kWord, 2, *seq, NameSet{}}, clk, LocalContext{},
                               LocalContext{}));
}

TEST(ExtendedBooleans, MatchedRejectsClockTickBeforeJ) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  const Word kWord{A({"a"}), A({"clk"}), A({"clk"})};
  EXPECT_TRUE(
      MatchedOutputs({kWord, 2, *seq, NameSet{}}, clk, LocalContext{}).empty());
}

TEST(ExtendedBooleans, MatchedRequiresAStrictlyEarlierTrigger) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  const Word kWord{A({"a"})};
  EXPECT_TRUE(
      MatchedOutputs({kWord, 0, *seq, NameSet{}}, clk, LocalContext{}).empty());
}

TEST(ExtendedBooleans, MatchedAllowsAdjacentTriggerAndTick) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  const Word kWord{A({"a"}), A({"clk"})};
  EXPECT_TRUE(MatchedSatisfies({kWord, 1, *seq, NameSet{}}, clk, LocalContext{},
                               LocalContext{}));
}

TEST(ExtendedBooleans, MatchedCarriesTheTriggeredOutputContext) {
  auto seq = Samp("v");
  auto clk = BoolAtom("clk");
  const Word kWord{A({"x"}), A({"clk"})};
  EXPECT_TRUE(SameContexts(
      MatchedOutputs({kWord, 1, *seq, NameSet{"v"}}, clk, LocalContext{}),
      {LocalContext{{"v", A({"x"})}}}));
  EXPECT_TRUE(SameContexts(
      MatchedOutputs({kWord, 1, *seq, NameSet{}}, clk, LocalContext{}),
      {LocalContext{}}));
}

TEST(ExtendedBooleans, TriggeredPredicateRejectsWrongOutputContext) {
  auto seq = Samp("v");
  const Word kWord{A({"x"})};
  EXPECT_TRUE(TriggeredSatisfies({kWord, 0, *seq, NameSet{"v"}}, LocalContext{},
                                 LocalContext{{"v", A({"x"})}}));
  EXPECT_FALSE(TriggeredSatisfies({kWord, 0, *seq, NameSet{"v"}},
                                  LocalContext{},
                                  LocalContext{{"v", A({"y"})}}));
  EXPECT_FALSE(TriggeredSatisfies({kWord, 0, *seq, NameSet{"v"}},
                                  LocalContext{}, LocalContext{}));
}

TEST(ExtendedBooleans, MatchedRejectsOutOfRangePoint) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  const Word kWord{A({"a"}), A({"clk"})};
  EXPECT_TRUE(
      MatchedOutputs({kWord, 2, *seq, NameSet{}}, clk, LocalContext{}).empty());
}

TEST(ExtendedBooleans, MatchedRequiresTriggerNotJustClock) {
  auto seq = Bool("a");
  auto clk = BoolAtom("clk");
  const Word kWord{A({}), A({"clk"})};
  EXPECT_TRUE(
      MatchedOutputs({kWord, 1, *seq, NameSet{}}, clk, LocalContext{}).empty());
}

TEST(ExtendedBooleans, TriggeredDecidesAClockedSequenceThroughItsRewrite) {
  auto seq = SeqClock(BoolAtom("clk"), SeqConcat(Bool("a"), Bool("b")));
  const Word kWord{A({"a", "clk"}), A({"x"}), A({"b", "clk"}), A({"b"})};
  EXPECT_TRUE(TriggeredSatisfies({kWord, 2, *seq, NameSet{}}, LocalContext{},
                                 LocalContext{}));
  EXPECT_TRUE(
      TriggeredOutputs({kWord, 0, *seq, NameSet{}}, LocalContext{}).empty());
  EXPECT_TRUE(
      TriggeredOutputs({kWord, 1, *seq, NameSet{}}, LocalContext{}).empty());
  EXPECT_TRUE(
      TriggeredOutputs({kWord, 3, *seq, NameSet{}}, LocalContext{}).empty());
}

TEST(ExtendedBooleans,
     TheExpressionsAreReadIntoAWordForThePrecedingSubclauses) {
  auto seq = SeqConcat(Bool("a"), Bool("b"));
  auto triggered = TriggeredExpression(seq, NameSet{});
  auto matched = MatchedExpression(seq, NameSet{}, BoolAtom("clk"));
  const Word kWord{A({"a"}), A({"b"}), A({"x"}), A({"clk"})};
  EXPECT_EQ(triggered(kWord, 0), false);
  EXPECT_EQ(triggered(kWord, 1), true);
  EXPECT_EQ(triggered(kWord, 2), false);
  EXPECT_EQ(triggered(kWord, 3), false);
  EXPECT_EQ(triggered(kWord, 4), std::nullopt);
  EXPECT_EQ(matched(kWord, 1), false);
  EXPECT_EQ(matched(kWord, 2), false);
  EXPECT_EQ(matched(kWord, 3), true);
  EXPECT_EQ(matched(kWord, 4), std::nullopt);
  const Word kRead = WordWithExtendedAtom(kWord, "tr", triggered);
  EXPECT_EQ(kRead[1].atoms, NameSet({"b", "tr"}));
  EXPECT_EQ(kRead[2].atoms, NameSet({"x"}));
  auto p = PropStrong(SeqConcat(SeqBoolean(BoolTrue()), Bool("tr")));
  EXPECT_TRUE(NeutrallySatisfies(kRead, *p));
  EXPECT_FALSE(NeutrallySatisfies(kWord, *p));
  const Word kMatched = WordWithExtendedAtom(kWord, "m", matched);
  EXPECT_EQ(kMatched[3].atoms, NameSet({"clk", "m"}));
  EXPECT_EQ(kMatched[2].atoms, NameSet({"x"}));
}

}  // namespace
