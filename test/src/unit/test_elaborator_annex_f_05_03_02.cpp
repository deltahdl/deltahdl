#include <gtest/gtest.h>

#include <cstddef>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_finite_word_satisfaction.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter L(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto BoolSeq(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

auto InitialStrongAThenB() {
  return AssertionWithClock(
      AssertionStatement::Activation::kInitial,
      AssertionStatement::Role::kAssert, BoolTrue(),
      TopProperty(PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b")))));
}

auto InitialWeakAThenB() {
  return AssertionWithClock(
      AssertionStatement::Activation::kInitial,
      AssertionStatement::Role::kAssert, BoolTrue(),
      TopProperty(PropWeak(SeqConcat(BoolSeq("a"), BoolSeq("b")))));
}

TEST(FiniteWordSatisfaction, WeakCompletesWithTheTopTail) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(WeaklySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_TRUE(
      WeaklySatisfiesByFiniteWord(Word{L({"a"}), L({"b"})}, *BoolTrue(), *a));
  EXPECT_FALSE(WeaklySatisfiesByFiniteWord(Word{L({"x"})}, *BoolTrue(), *a));
}

TEST(FiniteWordSatisfaction, StrongCompletesWithTheBottomTail) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(
      StronglySatisfiesByFiniteWord(Word{L({"a"}), L({"b"})}, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
}

TEST(FiniteWordSatisfaction, HoldsStronglyWhenStrongSatisfactionHolds) {
  auto a = InitialStrongAThenB();
  EXPECT_EQ(CheckFiniteWord(Word{L({"a"}), L({"b"})}, *BoolTrue(), *a),
            FiniteWordVerdict::kHoldsStrongly);
}

TEST(FiniteWordSatisfaction, FailsWhenNotEvenWeaklySatisfied) {
  auto a = InitialStrongAThenB();
  EXPECT_EQ(CheckFiniteWord(Word{L({"x"})}, *BoolTrue(), *a),
            FiniteWordVerdict::kFails);
}

TEST(FiniteWordSatisfaction, PendingWhenWeakHoldsButNeutralDoesNot) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(WeaklySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWord(Word{L({"a"})}, *BoolTrue(), *a),
            FiniteWordVerdict::kPending);
}

TEST(FiniteWordSatisfaction, HoldsWithoutStrengthWhenNeutralButNotStrong) {
  auto a = InitialWeakAThenB();
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWord(Word{L({"a"})}, *BoolTrue(), *a),
            FiniteWordVerdict::kHolds);
}

TEST(FiniteWordSatisfaction, WeakAndStrongDifferOnTheEmptyWord) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(WeaklySatisfiesByFiniteWord(Word{}, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(Word{}, *BoolTrue(), *a));
}

TEST(FiniteWordSatisfaction, EmptyWordHoldsWithoutStrength) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{}, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(Word{}, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWord(Word{}, *BoolTrue(), *a),
            FiniteWordVerdict::kHolds);
}

TEST(FiniteWordSatisfaction, VerdictLabelsMatchTheStandard) {
  EXPECT_STREQ(FiniteWordVerdictLabel(FiniteWordVerdict::kHoldsStrongly),
               "Holds strongly");
  EXPECT_STREQ(FiniteWordVerdictLabel(FiniteWordVerdict::kFails), "Fails");
  EXPECT_STREQ(FiniteWordVerdictLabel(FiniteWordVerdict::kHolds),
               "Holds (but does not hold strongly)");
  EXPECT_STREQ(FiniteWordVerdictLabel(FiniteWordVerdict::kPending), "Pending");
}

using Activation = AssertionStatement::Activation;
using Role = AssertionStatement::Role;

TEST(FiniteWordSatisfaction, TheTailHasActivationPointsOfItsOwn) {
  auto a = AssertionWithClock(
      Activation::kAlways, Role::kAssert, BoolTrue(),
      TopProperty(PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b")))));
  const Word kWord{L({"a"})};
  EXPECT_FALSE(NeutrallySatisfiesAssertion(kWord, *BoolTrue(), *a));
  EXPECT_TRUE(WeaklySatisfiesByFiniteWord(kWord, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(kWord, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWord(kWord, *BoolTrue(), *a),
            FiniteWordVerdict::kPending);
}

Word Completed(const Word& word, const Letter& tail, std::size_t count) {
  Word out = word;
  for (std::size_t i = 0; i < count; ++i) {
    out.push_back(tail);
  }
  return out;
}

TEST(FiniteWordSatisfaction, EveryPointOfTheBottomTailSeesTheWholeTail) {
  auto a = AssertionWithClock(
      Activation::kInitial, Role::kCover, BoolTrue(),
      TopProperty(PropNot(PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b"))))));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{}, *BoolTrue(), *a));
  EXPECT_FALSE(WeaklySatisfiesByFiniteWord(Word{}, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(Word{}, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWord(Word{}, *BoolTrue(), *a),
            FiniteWordVerdict::kFails);
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Completed(Word{}, LetterBottom(), 16),
                                          *BoolTrue(), *a));
}

TEST(FiniteWordSatisfaction, EachVerdictHasTheConditionTheSubclauseStates) {
  auto a = InitialStrongAThenB();
  const Word kAB{L({"a"}), L({"b"})};
  const Word kA{L({"a"})};
  const Word kX{L({"x"})};
  EXPECT_TRUE(FiniteWordVerdictCondition(FiniteWordVerdict::kHoldsStrongly, kAB,
                                         *BoolTrue(), *a));
  EXPECT_FALSE(FiniteWordVerdictCondition(FiniteWordVerdict::kHoldsStrongly, kA,
                                          *BoolTrue(), *a));
  EXPECT_TRUE(FiniteWordVerdictCondition(FiniteWordVerdict::kFails, kX,
                                         *BoolTrue(), *a));
  EXPECT_FALSE(FiniteWordVerdictCondition(FiniteWordVerdict::kFails, kA,
                                          *BoolTrue(), *a));
  EXPECT_TRUE(FiniteWordVerdictCondition(FiniteWordVerdict::kPending, kA,
                                         *BoolTrue(), *a));
  EXPECT_FALSE(FiniteWordVerdictCondition(FiniteWordVerdict::kPending, kAB,
                                          *BoolTrue(), *a));
  auto weak = InitialWeakAThenB();
  EXPECT_TRUE(FiniteWordVerdictCondition(FiniteWordVerdict::kHolds, kA,
                                         *BoolTrue(), *weak));
  EXPECT_FALSE(FiniteWordVerdictCondition(FiniteWordVerdict::kHolds, kAB,
                                          *BoolTrue(), *weak));
  EXPECT_FALSE(FiniteWordVerdictCondition(FiniteWordVerdict::kHolds, kA,
                                          *BoolTrue(), *a));
}

std::vector<std::shared_ptr<const AssertionStatement>> Assertions() {
  const auto kAThenB = SeqConcat(BoolSeq("a"), BoolSeq("b"));
  const std::vector<std::shared_ptr<const TopLevelProperty>> kTops{
      TopProperty(PropStrong(kAThenB)),
      TopProperty(PropWeak(kAThenB)),
      TopProperty(PropNot(PropStrong(kAThenB))),
      TopProperty(PropImplication(BoolSeq("a"), PropStrong(BoolSeq("b")))),
      TopProperty(PropNexttime(PropStrong(BoolSeq("b")))),
      TopProperty(PropUntil(PropWeak(BoolSeq("a")), PropStrong(BoolSeq("b")))),
      TopProperty(PropAcceptOn(BoolAtom("c"), PropStrong(kAThenB))),
      TopDisableIff(BoolAtom("d"), PropStrong(kAThenB)),
  };
  std::vector<std::shared_ptr<const AssertionStatement>> out;
  for (const auto& top : kTops) {
    for (Activation activation : {Activation::kInitial, Activation::kAlways}) {
      for (Role role : {Role::kAssert, Role::kCover}) {
        out.push_back(AssertionWithClock(activation, role, BoolTrue(), top));
      }
    }
  }
  out.push_back(AssertionWithClock(Activation::kAlways, Role::kAssert,
                                   BoolAtom("clk"),
                                   TopProperty(PropStrong(kAThenB))));
  return out;
}

std::vector<Word> Words() {
  return {Word{},
          Word{L({"a"})},
          Word{L({"a"}), L({"b"})},
          Word{L({"x"})},
          Word{L({"a"}), L({"x"})},
          Word{L({"a", "c"}), L({"x"})},
          Word{L({"a"}), L({"d"})},
          Word{L({"a"}), L({"b"}), L({"x"}), L({"a"})},
          Word{LetterTop()},
          Word{L({"a"}), LetterBottom()},
          Word{L({"a", "clk"}), L({"b"})},
          Word{L({"a", "clk"}), L({"x"}), L({"b", "clk"})}};
}

TEST(FiniteWordSatisfaction,
     WeakSatisfactionIsNeutralSatisfactionOfTheTopCompletion) {
  const std::size_t kRun = 16;
  bool weak_true = false;
  bool weak_false = false;
  for (const auto& a : Assertions()) {
    for (const Word& w : Words()) {
      const bool kWeak = WeaklySatisfiesByFiniteWord(w, *BoolTrue(), *a);
      EXPECT_EQ(kWeak, NeutrallySatisfiesAssertion(
                           Completed(w, LetterTop(), kRun), *BoolTrue(), *a));
      weak_true |= kWeak;
      weak_false |= !kWeak;
    }
  }
  EXPECT_TRUE(weak_true && weak_false);
}

std::vector<FiniteWordVerdict> VerdictsHolding(const Word& word,
                                               const AssertionStatement& a) {
  const std::vector<FiniteWordVerdict> kVerdicts{
      FiniteWordVerdict::kHoldsStrongly, FiniteWordVerdict::kFails,
      FiniteWordVerdict::kHolds, FiniteWordVerdict::kPending};
  std::vector<FiniteWordVerdict> out;
  for (FiniteWordVerdict verdict : kVerdicts) {
    if (FiniteWordVerdictCondition(verdict, word, *BoolTrue(), a)) {
      out.push_back(verdict);
    }
  }
  return out;
}

TEST(FiniteWordSatisfaction, TheVerdictIsTheOneConditionThatHolds) {
  std::set<FiniteWordVerdict> seen;
  for (const auto& a : Assertions()) {
    for (const Word& w : Words()) {
      const std::vector<FiniteWordVerdict> kHolding = VerdictsHolding(w, *a);
      ASSERT_EQ(kHolding.size(), 1U);
      EXPECT_EQ(kHolding[0], CheckFiniteWord(w, *BoolTrue(), *a));
      seen.insert(kHolding[0]);
    }
  }
  EXPECT_EQ(seen.size(), 4U);
}

TEST(FiniteWordSatisfaction, TheEnablingConditionReachesBothRelations) {
  auto a = AssertionWithClock(Activation::kAlways, Role::kAssert, BoolTrue(),
                              TopProperty(PropStrong(BoolSeq("a"))));
  const Word kX{L({"x"})};
  EXPECT_TRUE(WeaklySatisfiesByFiniteWord(kX, *BoolAtom("b"), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(kX, *BoolAtom("b"), *a));
  EXPECT_EQ(CheckFiniteWord(kX, *BoolAtom("b"), *a), FiniteWordVerdict::kHolds);
  EXPECT_EQ(CheckFiniteWord(kX, *BoolTrue(), *a), FiniteWordVerdict::kFails);
  EXPECT_EQ(CheckFiniteWord(Word{L({"b"})}, *BoolAtom("b"), *a),
            FiniteWordVerdict::kFails);
}

}  // namespace
