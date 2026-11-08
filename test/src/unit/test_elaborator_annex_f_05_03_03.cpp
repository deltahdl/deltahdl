#include <gtest/gtest.h>

#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_vacuity.h"

using namespace delta;

namespace {

Letter L(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

auto Strong(const std::string& name) { return PropStrong(Bs(name)); }

auto Trig(const std::string& name) {
  return PropImplication(Bs(name), Strong("t"));
}

TEST(NonVacuity, StrongAndWeakAreAlwaysNonvacuous) {
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"a"})}, *Strong("a")));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{}, *Strong("a")));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"a"})}, *PropWeak(Bs("a"))));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{}, *PropWeak(Bs("a"))));
}

TEST(NonVacuity, ParenthesisIsTransparent) {
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"a"})}, *PropParen(Trig("a"))));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *PropParen(Trig("a"))));
}

TEST(NonVacuity, ImplicationNeedsTheTriggerToMatch) {
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"a"})}, *Trig("a")));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *Trig("a")));
}

TEST(NonVacuity, DisjunctionIsNonvacuousWhenEitherSideIs) {
  auto p = PropOr(Trig("a"), Trig("a"));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *p));
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"x"})}, *PropOr(Trig("a"), Strong("s"))));
}

TEST(NonVacuity, ConjunctionIsNonvacuousWhenEitherSideIs) {
  auto vacuous_side = Trig("a");
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *vacuous_side));
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"x"})}, *PropAnd(Strong("s"), Trig("a"))));
}

TEST(NonVacuity, NegationEvaluatesOnTheComplement) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{LetterBottom()}, *Trig("a")));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{LetterBottom()}, *PropNot(Trig("a"))));
}

TEST(NonVacuity, NexttimeRequiresANonemptyWord) {
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"a"})}, *PropNexttime(Strong("b"))));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{}, *PropNexttime(Strong("b"))));
}

TEST(NonVacuity, UntilNeedsAnOperandToBecomeNonvacuous) {
  auto until = PropUntil(Trig("a"), Trig("a"));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *until));
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"a"})}, *PropUntil(Trig("a"), Trig("a"))));
}

TEST(NonVacuity, UntilWitnessMayFollowANonvacuousGuardPrefix) {
  auto until = PropUntil(Trig("a"), PropNot(Trig("a")));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"x"}), L({"a"})}, *until));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"}), L({"a"})},
                                     *PropUntil(Trig("a"), Trig("a"))));
}

TEST(NonVacuity, AcceptOnHoldsViaTheNoAbortAlternative) {
  auto p = PropAcceptOn(BoolAtom("b"), Strong("s"));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"s"})}, *p));
}

TEST(NonVacuity, AcceptOnHoldsViaThePrefixAlternativeWhenBOccurs) {
  auto p = PropAcceptOn(BoolAtom("b"), Strong("s"));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"s"}), L({"b"})}, *p));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"x"}), L({"b"})}, *p));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"b", "s"})}, *p));
}

TEST(NonVacuity, AcceptOnInheritsAVacuousOperand) {
  auto p = PropAcceptOn(BoolAtom("b"), Trig("a"));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *p));
}

TEST(NonVacuity, DisableIffTopLevelUsesTheAbortShape) {
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevel(
      Word{L({"s"})}, *TopDisableIff(BoolAtom("b"), Strong("s"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesTopLevel(
      Word{L({"x"})}, *TopDisableIff(BoolAtom("b"), Trig("a"))));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesTopLevel(Word{L({"a"})}, *TopProperty(Trig("a"))));
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevel(Word{L({"a"})},
                                            *TopParen(TopProperty(Trig("a")))));
}

TEST(NonVacuity, NonvacuousSatisfactionRequiresBothRelations) {
  EXPECT_TRUE(NeutrallySatisfies(Word{L({"s"})}, *Strong("s")));
  EXPECT_TRUE(SatisfiesNonVacuously(Word{L({"s"})}, *Strong("s")));
}

TEST(NonVacuity, NonvacuousSatisfactionRejectsAVacuousPass) {
  EXPECT_TRUE(NeutrallySatisfies(Word{L({"x"})}, *Trig("a")));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *Trig("a")));
  EXPECT_FALSE(SatisfiesNonVacuously(Word{L({"x"})}, *Trig("a")));
}

TEST(NonVacuity, TopLevelNonvacuousSatisfactionCombinesBothRelations) {
  auto top = TopProperty(Trig("a"));
  EXPECT_FALSE(SatisfiesTopLevelNonVacuously(Word{L({"x"})}, *top));
  EXPECT_TRUE(
      SatisfiesTopLevelNonVacuously(Word{L({"s"})}, *TopProperty(Strong("s"))));
}

TEST(NonVacuity, ImplicationIsVacuousOnTheEmptyWord) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{}, *Trig("a")));
}

TEST(NonVacuity, UntilIsVacuousOnTheEmptyWord) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{}, *PropUntil(Trig("a"), Trig("a"))));
}

TEST(NonVacuity, ConjunctionIsVacuousWhenBothSidesAre) {
  EXPECT_FALSE(
      NonVacuouslyEvaluates(Word{L({"x"})}, *PropAnd(Trig("a"), Trig("a"))));
}

TEST(NonVacuity, NexttimeDefersToTheSuffixNonVacuity) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"a"})}, *PropNexttime(Trig("a"))));
}

TEST(NonVacuity, AcceptOnOnTheEmptyWordFollowsTheOperand) {
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{}, *PropAcceptOn(BoolAtom("b"), Strong("s"))));
  EXPECT_FALSE(
      NonVacuouslyEvaluates(Word{}, *PropAcceptOn(BoolAtom("b"), Trig("a"))));
}

TEST(NonVacuity, DisableIffOnTheEmptyWordFollowsTheOperand) {
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevel(
      Word{}, *TopDisableIff(BoolAtom("b"), Strong("s"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesTopLevel(
      Word{}, *TopDisableIff(BoolAtom("b"), Trig("a"))));
}

TEST(NonVacuity, IffIsNonvacuousWhenEitherSideIs) {
  auto p1 = Trig("a");
  auto p2 = Trig("b");
  EXPECT_TRUE(NonVacuouslyEvaluatesIff(Word{L({"a"})}, *p1, *p2));
  EXPECT_TRUE(NonVacuouslyEvaluatesIff(Word{L({"b"})}, *p1, *p2));
  EXPECT_FALSE(NonVacuouslyEvaluatesIff(Word{L({"x"})}, *p1, *p2));
  EXPECT_FALSE(NonVacuouslyEvaluatesIff(Word{LetterBottom()}, *p1, *p2));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{LetterBottom()}, *PropIff(p1, p2)));
}

TEST(NonVacuity, ImpliesNeedsTheAntecedentToHoldNonvacuously) {
  auto p1 = Trig("a");
  auto p2 = Strong("s");
  EXPECT_TRUE(NonVacuouslyEvaluatesImplies(Word{L({"a", "t"})}, *p1, *p2));
  EXPECT_FALSE(NonVacuouslyEvaluatesImplies(Word{L({"a"})}, *p1, *p2));
  EXPECT_FALSE(NonVacuouslyEvaluatesImplies(Word{L({"x"})}, *p1, *p2));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"x"})}, *PropImplies(p1, p2)));
  EXPECT_FALSE(NonVacuouslyEvaluatesImplies(Word{L({"s"})}, *p2, *p1));
  EXPECT_TRUE(NonVacuouslyEvaluatesImplies(Word{L({"s", "a"})}, *p2, *p1));
}

TEST(NonVacuity, SUntilSharesTheUntilRule) {
  auto p1 = Trig("a");
  auto p2 = PropNot(Trig("a"));
  auto until = PropUntil(p1, p2);
  const std::vector<Word> kWords{Word{L({"x"}), L({"a"})},
                                 Word{L({"x"}), L({"x"})}, Word{L({"a"})},
                                 Word{}};
  for (const Word& w : kWords) {
    EXPECT_EQ(NonVacuouslyEvaluatesSUntil(w, *p1, *p2),
              NonVacuouslyEvaluates(w, *until));
  }
  EXPECT_TRUE(NonVacuouslyEvaluatesSUntil(Word{L({"x"}), L({"a"})}, *p1, *p2));
  EXPECT_FALSE(NonVacuouslyEvaluatesSUntil(Word{L({"x"}), L({"x"})}, *p1, *p2));
}

TEST(NonVacuity, AlwaysNeedsAWitnessBeforeWhichPHolds) {
  const Word kXAt{L({"x"}), L({"a", "t"})};
  EXPECT_TRUE(NonVacuouslyEvaluatesAlways(kXAt, *Trig("a")));
  EXPECT_FALSE(
      NonVacuouslyEvaluatesAlways(Word{L({"x"}), L({"x"})}, *Trig("a")));
  EXPECT_FALSE(NonVacuouslyEvaluatesAlways(Word{}, *Trig("a")));
  EXPECT_FALSE(NonVacuouslyEvaluatesAlways(kXAt, *PropNot(Trig("a"))));
  EXPECT_TRUE(NonVacuouslyEvaluates(kXAt, *PropAlways(PropNot(Trig("a")))));
}

TEST(NonVacuity, AlwaysRangeIsBoundedByItsIndicesAlone) {
  const Word kXAt{L({"x"}), L({"a", "t"})};
  const Word kXX{L({"x"}), L({"x"})};
  EXPECT_FALSE(NonVacuouslyEvaluatesAlwaysRange(kXAt, *Trig("a"), 0, 0));
  EXPECT_TRUE(NonVacuouslyEvaluatesAlwaysRange(kXAt, *Trig("a"), 1, 1));
  EXPECT_TRUE(NonVacuouslyEvaluatesAlwaysRange(kXAt, *Trig("a"), 1, 2));
  EXPECT_FALSE(
      NonVacuouslyEvaluatesAlwaysRange(kXAt, *PropNot(Trig("a")), 0, 1));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesAlwaysRange(kXAt, *PropNot(Trig("a")), 1, 1));
  EXPECT_TRUE(NonVacuouslyEvaluatesAlwaysRange(kXX, *Strong("s"), 3, 4));
  EXPECT_FALSE(NonVacuouslyEvaluatesAlwaysRange(kXX, *Trig("a"), 3, 4));
  const std::vector<Word> kWords{kXAt, kXX};
  for (const Word& w : kWords) {
    for (unsigned int m = 0; m < 3; ++m) {
      EXPECT_EQ(NonVacuouslyEvaluatesSAlwaysRange(w, *Trig("a"), m, 3),
                NonVacuouslyEvaluatesAlwaysRange(w, *Trig("a"), m, 3));
    }
  }
}

TEST(NonVacuity, SEventuallyNeedsPToFailBeforeItsWitness) {
  const Word kXAt{L({"x"}), L({"a", "t"})};
  EXPECT_TRUE(NonVacuouslyEvaluatesSEventually(kXAt, *PropNot(Trig("a"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesSEventually(kXAt, *Trig("a")));
  EXPECT_TRUE(NonVacuouslyEvaluates(kXAt, *PropSEventually(Trig("a"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesSEventually(Word{L({"x"}), L({"x"})},
                                                *PropNot(Trig("a"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesSEventually(Word{}, *PropNot(Trig("a"))));
}

TEST(NonVacuity, EventuallyRangeIsBoundedByItsIndicesAlone) {
  const Word kXAt{L({"x"}), L({"a", "t"})};
  auto neg = PropNot(Trig("a"));
  EXPECT_TRUE(NonVacuouslyEvaluatesEventuallyRange(kXAt, *neg, 1, 1));
  EXPECT_TRUE(NonVacuouslyEvaluatesEventuallyRange(kXAt, *neg, 0, 1));
  EXPECT_FALSE(NonVacuouslyEvaluatesEventuallyRange(kXAt, *neg, 0, 0));
  EXPECT_FALSE(NonVacuouslyEvaluatesEventuallyRange(kXAt, *Trig("a"), 0, 1));
  EXPECT_TRUE(NonVacuouslyEvaluatesEventuallyRange(kXAt, *Trig("a"), 1, 1));
  for (unsigned int m = 0; m < 3; ++m) {
    EXPECT_EQ(NonVacuouslyEvaluatesSEventuallyRange(kXAt, *Trig("a"), m, 3),
              NonVacuouslyEvaluatesEventuallyRange(kXAt, *Trig("a"), m, 3));
    EXPECT_EQ(NonVacuouslyEvaluatesSEventuallyRange(kXAt, *neg, m, 3),
              NonVacuouslyEvaluatesEventuallyRange(kXAt, *neg, m, 3));
  }
}

TEST(NonVacuity, RejectOnSharesTheAbortShape) {
  auto b = BoolAtom("b");
  EXPECT_TRUE(NonVacuouslyEvaluatesRejectOn(Word{L({"x"})}, *b, *Strong("s")));
  EXPECT_TRUE(NonVacuouslyEvaluatesRejectOn(Word{L({"s"}), L({"b"})}, *b,
                                            *Strong("s")));
  EXPECT_FALSE(
      NonVacuouslyEvaluatesRejectOn(Word{L({"b", "s"})}, *b, *Strong("s")));
  EXPECT_FALSE(
      NonVacuouslyEvaluatesRejectOn(Word{LetterTop()}, *b, *Strong("s")));
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{LetterTop()}, *PropRejectOn(b, Strong("s"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesRejectOn(Word{L({"x"})}, *b, *Trig("a")));
}

TEST(NonVacuity, TheOtherDerivedOperatorsUnroll) {
  auto p = PropSNexttime(Trig("a"));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"x"}), L({"a", "t"})}, *p));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"a", "t"}), L({"x"})}, *p));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{}, *p));
}

}  // namespace
