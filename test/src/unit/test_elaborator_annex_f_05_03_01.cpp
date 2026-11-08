#include <gtest/gtest.h>

#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto BoolSeq(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

auto ClockedStrongA() {
  return ClkClock(BoolAtom("clk"), ClkStrong(SeqBoolean(BoolAtom("a"))));
}

TEST(NeutralSatisfaction, StrongHoldsWhenSomePrefixTightlyMatches) {
  auto p = PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *p));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"}), A({"c"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"}), A({"b"})}, *p));
}

TEST(NeutralSatisfaction, WeakAcceptsAnUnfinishedSequenceStrongRejects) {
  auto strong = PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b")));
  auto weak = PropWeak(SeqConcat(BoolSeq("a"), BoolSeq("b")));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *strong));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *weak));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *weak));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"})}, *weak));
}

TEST(NeutralSatisfaction, ParenthesisIsTransparent) {
  auto p = PropParen(PropStrong(BoolSeq("a")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"})}, *p));
}

TEST(NeutralSatisfaction, NotEvaluatesAgainstTheComplementWord) {
  auto strong = PropStrong(BoolSeq("a"));
  auto negated = PropNot(PropStrong(BoolSeq("a")));
  EXPECT_TRUE(NeutrallySatisfies(Word{LetterTop()}, *strong));
  EXPECT_TRUE(NeutrallySatisfies(Word{LetterTop()}, *negated));
  EXPECT_FALSE(NeutrallySatisfies(Word{LetterBottom()}, *strong));
  EXPECT_FALSE(NeutrallySatisfies(Word{LetterBottom()}, *negated));
}

TEST(NeutralSatisfaction, ImplicationDischargesConsequentAtEachMatch) {
  auto impl = PropImplication(BoolSeq("a"), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a", "b"})}, *impl));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *impl));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"})}, *impl));
}

TEST(NeutralSatisfaction, OrTakesEitherOperand) {
  auto p = PropOr(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *p));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"b"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"})}, *p));
}

TEST(NeutralSatisfaction, AndRequiresBothOperands) {
  auto p = PropAnd(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a", "b"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *p));
}

TEST(NeutralSatisfaction, NexttimeShiftsPastTheFirstLetter) {
  auto p = PropNexttime(PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *p));
}

TEST(NeutralSatisfaction, UntilHoldsUntilTheReleasingSuffix) {
  auto p = PropUntil(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"a"}), A({"b"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"x"})}, *p));
}

TEST(NeutralSatisfaction, AcceptOnPassesOnAbortCompletion) {
  auto p = PropAcceptOn(BoolAtom("r"), PropStrong(BoolSeq("c")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"c"})}, *p));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"r"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"})}, *p));
}

TEST(NeutralSatisfaction, TopLevelBarePropertyDefersToTheProperty) {
  auto t = TopProperty(PropStrong(BoolSeq("a")));
  EXPECT_TRUE(NeutrallySatisfiesTopLevel(Word{A({"a"})}, *t));
  EXPECT_FALSE(NeutrallySatisfiesTopLevel(Word{A({"x"})}, *t));
}

TEST(NeutralSatisfaction, TopLevelDisableIffSatisfaction) {
  auto t = TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a")));
  EXPECT_TRUE(NeutrallySatisfiesTopLevel(Word{A({"a"})}, *t));
  EXPECT_FALSE(NeutrallySatisfiesTopLevel(Word{A({"d"})}, *t));
  EXPECT_TRUE(NeutrallySatisfiesTopLevel(Word{A({"a"}), A({"d"})}, *t));
}

TEST(NeutralSatisfaction, TopLevelParenthesisIsTransparent) {
  auto t = TopParen(TopProperty(PropStrong(BoolSeq("a"))));
  EXPECT_TRUE(NeutrallySatisfiesTopLevel(Word{A({"a"})}, *t));
  EXPECT_FALSE(NeutrallySatisfiesTopLevel(Word{A({"x"})}, *t));
}

TEST(Disabling, BarePropertyIsNeverDisabled) {
  auto t = TopProperty(PropStrong(BoolSeq("a")));
  EXPECT_FALSE(DisablesTopLevel(Word{A({"a"})}, *t));
  EXPECT_FALSE(DisablesTopLevel(Word{A({"x"})}, *t));
}

TEST(Disabling, DisableIffIsDisabledWhenCompletionsDiverge) {
  auto t = TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a")));
  EXPECT_TRUE(DisablesTopLevel(Word{A({"d"})}, *t));
  EXPECT_FALSE(DisablesTopLevel(Word{A({"a"})}, *t));
}

TEST(Disabling, ParenthesizedTopLevelPropagatesDisabling) {
  auto t = TopParen(TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a"))));
  EXPECT_TRUE(DisablesTopLevel(Word{A({"d"})}, *t));
}

TEST(Disabling, PassDisabledFailTrichotomy) {
  auto bare = TopProperty(PropStrong(BoolSeq("a")));
  EXPECT_TRUE(PassesTopLevel(Word{A({"a"})}, *bare));
  EXPECT_FALSE(IsDisabledTopLevel(Word{A({"a"})}, *bare));
  EXPECT_FALSE(FailsTopLevel(Word{A({"a"})}, *bare));

  EXPECT_FALSE(PassesTopLevel(Word{A({"x"})}, *bare));
  EXPECT_FALSE(IsDisabledTopLevel(Word{A({"x"})}, *bare));
  EXPECT_TRUE(FailsTopLevel(Word{A({"x"})}, *bare));

  auto guarded = TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a")));
  EXPECT_FALSE(PassesTopLevel(Word{A({"d"})}, *guarded));
  EXPECT_TRUE(IsDisabledTopLevel(Word{A({"d"})}, *guarded));
  EXPECT_FALSE(FailsTopLevel(Word{A({"d"})}, *guarded));
}

TEST(NeutralSatisfaction, NexttimeHoldsVacuouslyOnTheEmptyWord) {
  auto p = PropNexttime(PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{}, *p));
}

TEST(NeutralSatisfaction, UntilHoldsWhenLeftOperandHoldsThroughout) {
  auto p = PropUntil(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"a"})}, *p));
}

TEST(NeutralSatisfaction, NotNegatesTheVerdictOverAtomLetters) {
  auto negated = PropNot(PropStrong(BoolSeq("a")));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *negated));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"})}, *negated));
}

TEST(NeutralSatisfaction, ImplicationEvaluatesConsequentOnTheOverlapSuffix) {
  auto impl =
      PropImplication(SeqConcat(BoolSeq("a"), BoolSeq("b")),
                      PropStrong(SeqConcat(BoolSeq("b"), BoolSeq("c"))));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"}), A({"c"})}, *impl));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"b"}), A({"x"})}, *impl));
}

TEST(NeutralSatisfaction, AcceptOnCompletesNonemptyPrefixAtLaterAbort) {
  auto p = PropAcceptOn(BoolAtom("r"),
                        PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b"))));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"r"})}, *p));
}

TEST(NeutralSatisfaction, DisableIffFailsWhenPropertyFailsAndNothingDisables) {
  auto t = TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a")));
  EXPECT_FALSE(NeutrallySatisfiesTopLevel(Word{A({"x"})}, *t));
}

TEST(Disabling, DisableIffNotDisabledWhenCompletionsAgree) {
  auto t = TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a")));
  EXPECT_FALSE(DisablesTopLevel(Word{A({"a"}), A({"d"})}, *t));
  EXPECT_TRUE(PassesTopLevel(Word{A({"a"}), A({"d"})}, *t));
}

TEST(ClockedProperty, SatisfiedWhenSampledBooleanHoldsAtClockTick) {
  auto q = ClockedStrongA();
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(Word{A({"clk", "a"})}, *q));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(Word{A({"clk"})}, *q));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(Word{A({"a"})}, *q));
}

TEST(ClockedProperty, ClockIdlesUntilItsFirstTick) {
  auto q = ClockedStrongA();
  EXPECT_TRUE(
      NeutrallySatisfiesClockedProperty(Word{A({"x"}), A({"clk", "a"})}, *q));
  EXPECT_FALSE(
      NeutrallySatisfiesClockedProperty(Word{A({"x"}), A({"clk"})}, *q));
}

TEST(ClockedTopLevel, BarePropertyDefersToTheClockedProperty) {
  auto u = ClockedTopProperty(ClockedStrongA());
  EXPECT_TRUE(NeutrallySatisfiesTopLevelClocked(Word{A({"clk", "a"})}, *u));
  EXPECT_FALSE(NeutrallySatisfiesTopLevelClocked(Word{A({"clk"})}, *u));
}

TEST(ClockedTopLevel, DisableIffSatisfaction) {
  auto u = ClockedTopDisableIff(BoolAtom("d"), ClockedStrongA());
  EXPECT_TRUE(NeutrallySatisfiesTopLevelClocked(Word{A({"clk", "a"})}, *u));
  EXPECT_FALSE(NeutrallySatisfiesTopLevelClocked(Word{A({"d"})}, *u));
}

TEST(ClockedTopLevel, ParenthesisIsTransparent) {
  auto u = ClockedTopParen(ClockedTopProperty(ClockedStrongA()));
  EXPECT_TRUE(NeutrallySatisfiesTopLevelClocked(Word{A({"clk", "a"})}, *u));
  EXPECT_FALSE(NeutrallySatisfiesTopLevelClocked(Word{A({"clk"})}, *u));
}

TEST(ClockedTopLevel, DisableIffIsDisabledWhenCompletionsDiverge) {
  auto u = ClockedTopDisableIff(BoolAtom("d"), ClockedStrongA());
  EXPECT_TRUE(DisablesTopLevelClocked(Word{A({"d"})}, *u));
  EXPECT_FALSE(DisablesTopLevelClocked(Word{A({"clk", "a"})}, *u));
  EXPECT_FALSE(DisablesTopLevelClocked(Word{A({"clk", "a"})},
                                       *ClockedTopProperty(ClockedStrongA())));
}

TEST(ClockedTopLevel, PassDisabledFailTrichotomy) {
  auto bare = ClockedTopProperty(ClockedStrongA());
  EXPECT_TRUE(PassesTopLevelClocked(Word{A({"clk", "a"})}, *bare));
  EXPECT_FALSE(FailsTopLevelClocked(Word{A({"clk", "a"})}, *bare));
  EXPECT_TRUE(FailsTopLevelClocked(Word{A({"x"})}, *bare));

  auto guarded = ClockedTopDisableIff(BoolAtom("d"), ClockedStrongA());
  EXPECT_TRUE(IsDisabledTopLevelClocked(Word{A({"d"})}, *guarded));
  EXPECT_FALSE(FailsTopLevelClocked(Word{A({"d"})}, *guarded));
}

auto BodyStrong(const std::string& name) {
  return TopProperty(PropStrong(BoolSeq(name)));
}

TEST(Assertion, AlwaysClockedAssertChecksEveryClockTick) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kAlways,
                              AssertionStatement::Role::kAssert,
                              BoolAtom("clk"), BodyStrong("a"));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolTrue(), *a));
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"x"})}, *BoolTrue(), *a));
}

TEST(Assertion, AssumeSharesTheAssertDefinition) {
  auto assert_stmt = AssertionWithClock(AssertionStatement::Activation::kAlways,
                                        AssertionStatement::Role::kAssert,
                                        BoolAtom("clk"), BodyStrong("a"));
  auto assume_stmt = AssertionWithClock(AssertionStatement::Activation::kAlways,
                                        AssertionStatement::Role::kAssume,
                                        BoolAtom("clk"), BodyStrong("a"));
  for (const Word& w :
       {Word{A({"clk", "a"})}, Word{A({"clk"})}, Word{A({"x"})}}) {
    EXPECT_EQ(NeutrallySatisfiesAssertion(w, *BoolTrue(), *assert_stmt),
              NeutrallySatisfiesAssertion(w, *BoolTrue(), *assume_stmt));
  }
}

TEST(Assertion, AlwaysClockedCoverNeedsOnePassingTick) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kAlways,
                              AssertionStatement::Role::kCover, BoolAtom("clk"),
                              BodyStrong("a"));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"x"})}, *BoolTrue(), *a));
}

TEST(Assertion, InitialClockedAssertFiresAtFirstClockTick) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kInitial,
                              AssertionStatement::Role::kAssert,
                              BoolAtom("clk"), BodyStrong("a"));
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"x"}), A({"clk", "a"})},
                                          *BoolTrue(), *a));
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"x"}), A({"clk"})}, *BoolTrue(), *a));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"x"}), A({"y"})}, *BoolTrue(), *a));
}

TEST(Assertion, EnablingConditionGatesActivation) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kAlways,
                              AssertionStatement::Role::kAssert,
                              BoolAtom("clk"), BodyStrong("a"));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolAtom("en"), *a));
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "en"})}, *BoolAtom("en"), *a));
}

TEST(Assertion, ClockedTopBodyUsesTheIntrinsicClock) {
  auto cover = AssertionWithClockedTop(AssertionStatement::Activation::kAlways,
                                       AssertionStatement::Role::kCover,
                                       ClockedTopProperty(ClockedStrongA()));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolTrue(), *cover));
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"x"})}, *BoolTrue(), *cover));
}

TEST(WordSet, FeasibilityAndAssertSatisfaction) {
  EnabledAssertion assumption{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssume, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  std::vector<EnabledAssertion> assumptions{assumption};

  const Word kFeasible = {A({"clk", "a"})};
  const Word kInfeasible = {A({"clk"})};
  EXPECT_TRUE(WordIsFeasible(kFeasible, assumptions));
  EXPECT_FALSE(WordIsFeasible(kInfeasible, assumptions));

  std::vector<Word> words{kFeasible, kInfeasible};

  EnabledAssertion holds{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssert, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  EXPECT_TRUE(AssertSatisfiedOnWordSet(holds, words, assumptions));
  EXPECT_TRUE(HoldsGloballyOnWordSet(holds, words, assumptions));

  EnabledAssertion fails{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssert, BoolAtom("clk"),
                          BodyStrong("b")),
      BoolTrue()};
  EXPECT_FALSE(AssertSatisfiedOnWordSet(fails, words, assumptions));
}

TEST(WordSet, CoverSatisfactionNeedsOneFeasibleWitness) {
  std::vector<EnabledAssertion> no_assumptions;
  std::vector<Word> words{Word{A({"x"})}, Word{A({"clk", "a"})}};

  EnabledAssertion cover{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kCover, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  EXPECT_TRUE(CoverSatisfiedOnWordSet(cover, words, no_assumptions));

  EnabledAssertion uncovered{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kCover, BoolAtom("clk"),
                          BodyStrong("z")),
      BoolTrue()};
  EXPECT_FALSE(CoverSatisfiedOnWordSet(uncovered, words, no_assumptions));
}

TEST(Assertion, AlwaysAssertUUsesTheIntrinsicClock) {
  auto a = AssertionWithClockedTop(AssertionStatement::Activation::kAlways,
                                   AssertionStatement::Role::kAssert,
                                   ClockedTopProperty(ClockedStrongA()));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolTrue(), *a));
}

TEST(Assertion, InitialAssertUFiresOnlyAtIndexZero) {
  auto a = AssertionWithClockedTop(AssertionStatement::Activation::kInitial,
                                   AssertionStatement::Role::kAssert,
                                   ClockedTopProperty(ClockedStrongA()));
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"clk", "a"}), A({"x"})},
                                          *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolTrue(), *a));
}

TEST(Assertion, AlwaysAssumeUSharesAssertU) {
  auto assert_stmt = AssertionWithClockedTop(
      AssertionStatement::Activation::kAlways,
      AssertionStatement::Role::kAssert, ClockedTopProperty(ClockedStrongA()));
  auto assume_stmt = AssertionWithClockedTop(
      AssertionStatement::Activation::kAlways,
      AssertionStatement::Role::kAssume, ClockedTopProperty(ClockedStrongA()));
  for (const Word& w :
       {Word{A({"clk", "a"})}, Word{A({"clk"})}, Word{A({"x"})}}) {
    EXPECT_EQ(NeutrallySatisfiesAssertion(w, *BoolTrue(), *assert_stmt),
              NeutrallySatisfiesAssertion(w, *BoolTrue(), *assume_stmt));
  }
}

TEST(Assertion, InitialClockedAssumeSharesAssert) {
  auto assert_stmt = AssertionWithClock(
      AssertionStatement::Activation::kInitial,
      AssertionStatement::Role::kAssert, BoolAtom("clk"), BodyStrong("a"));
  auto assume_stmt = AssertionWithClock(
      AssertionStatement::Activation::kInitial,
      AssertionStatement::Role::kAssume, BoolAtom("clk"), BodyStrong("a"));
  for (const Word& w : {Word{A({"x"}), A({"clk", "a"})},
                        Word{A({"x"}), A({"clk"})}, Word{A({"x"}), A({"y"})}}) {
    EXPECT_EQ(NeutrallySatisfiesAssertion(w, *BoolTrue(), *assert_stmt),
              NeutrallySatisfiesAssertion(w, *BoolTrue(), *assume_stmt));
  }
}

TEST(Assertion, InitialAssumeUSharesAssertU) {
  auto assert_stmt = AssertionWithClockedTop(
      AssertionStatement::Activation::kInitial,
      AssertionStatement::Role::kAssert, ClockedTopProperty(ClockedStrongA()));
  auto assume_stmt = AssertionWithClockedTop(
      AssertionStatement::Activation::kInitial,
      AssertionStatement::Role::kAssume, ClockedTopProperty(ClockedStrongA()));
  for (const Word& w : {Word{A({"clk", "a"}), A({"x"})}, Word{A({"clk"})}}) {
    EXPECT_EQ(NeutrallySatisfiesAssertion(w, *BoolTrue(), *assert_stmt),
              NeutrallySatisfiesAssertion(w, *BoolTrue(), *assume_stmt));
  }
}

TEST(Assertion, InitialClockedCoverFiresAtFirstTick) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kInitial,
                              AssertionStatement::Role::kCover, BoolAtom("clk"),
                              BodyStrong("a"));
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"x"}), A({"clk", "a"})},
                                          *BoolTrue(), *a));
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"x"}), A({"clk"})}, *BoolTrue(), *a));
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"x"}), A({"y"})}, *BoolTrue(), *a));
}

TEST(Assertion, InitialCoverUFiresAtIndexZero) {
  auto a = AssertionWithClockedTop(AssertionStatement::Activation::kInitial,
                                   AssertionStatement::Role::kCover,
                                   ClockedTopProperty(ClockedStrongA()));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolTrue(), *a));
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolAtom("en"), *a));
}

TEST(ClockedTopLevel, ParenthesizedDisablingPropagates) {
  auto u =
      ClockedTopParen(ClockedTopDisableIff(BoolAtom("d"), ClockedStrongA()));
  EXPECT_TRUE(DisablesTopLevelClocked(Word{A({"d"})}, *u));
  EXPECT_FALSE(DisablesTopLevelClocked(Word{A({"clk", "a"})}, *u));
}

TEST(Assertion, AlwaysClockedAssertFailsWhenALaterTickFails) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kAlways,
                              AssertionStatement::Role::kAssert,
                              BoolAtom("clk"), BodyStrong("a"));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk", "a"}), A({"clk"})},
                                           *BoolTrue(), *a));
  EXPECT_TRUE(NeutrallySatisfiesAssertion(
      Word{A({"clk", "a"}), A({"clk", "a"})}, *BoolTrue(), *a));
}

TEST(Assertion, AlwaysClockedCoverFiresAtALaterTick) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kAlways,
                              AssertionStatement::Role::kCover, BoolAtom("clk"),
                              BodyStrong("a"));
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"clk"}), A({"clk", "a"})},
                                          *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"}), A({"clk"})},
                                           *BoolTrue(), *a));
}

TEST(NeutralSatisfaction, DisableIffUsesLeastSatisfyingIndex) {
  auto t = TopDisableIff(BoolAtom("d"),
                         PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b"))));
  EXPECT_FALSE(
      NeutrallySatisfiesTopLevel(Word{A({"a"}), A({"b", "d"}), A({"d"})}, *t));
  EXPECT_TRUE(
      NeutrallySatisfiesTopLevel(Word{A({"a"}), A({"b"}), A({"d"})}, *t));
}

TEST(NeutralSatisfaction, UntilReleasesImmediately) {
  auto p = PropUntil(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"b"})}, *p));
}

TEST(WordSet, VacuousWhenEveryWordIsInfeasible) {
  EnabledAssertion assumption{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssume, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  std::vector<EnabledAssertion> assumptions{assumption};
  std::vector<Word> words{Word{A({"clk"})}};

  EnabledAssertion assert_stmt{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssert, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  EXPECT_TRUE(AssertSatisfiedOnWordSet(assert_stmt, words, assumptions));
  EXPECT_TRUE(HoldsGloballyOnWordSet(assert_stmt, words, assumptions));

  EnabledAssertion cover_stmt{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kCover, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  EXPECT_FALSE(CoverSatisfiedOnWordSet(cover_stmt, words, assumptions));
}

TEST(WordSet, FeasibilityRequiresEveryAssumption) {
  EnabledAssertion assume_a{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssume, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  EnabledAssertion assume_b{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssume, BoolAtom("clk"),
                          BodyStrong("b")),
      BoolTrue()};
  std::vector<EnabledAssertion> assumptions{assume_a, assume_b};
  EXPECT_FALSE(WordIsFeasible(Word{A({"clk", "a"})}, assumptions));
  EXPECT_TRUE(WordIsFeasible(Word{A({"clk", "a", "b"})}, assumptions));
}

}  // namespace
