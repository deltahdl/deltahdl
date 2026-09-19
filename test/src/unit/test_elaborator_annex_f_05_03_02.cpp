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

// initial @( 1 ) strong( a ##1 b ): a single activation at index 0 whose body
// is the strong sequence a then b. Under T^p(., 1) the constant clock
// collapses, so the body holds exactly when a ##1 b is tightly matched within
// the word.
auto InitialStrongAThenB() {
  return AssertionWithClock(
      AssertionStatement::Activation::kInitial,
      AssertionStatement::Role::kAssert, BoolTrue(),
      TopProperty(PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b")))));
}

// initial @( 1 ) weak( a ##1 b ): the same obligation in its weak form, which
// tolerates the sequence still being open at the end of the word.
auto InitialWeakAThenB() {
  return AssertionWithClock(
      AssertionStatement::Activation::kInitial,
      AssertionStatement::Role::kAssert, BoolTrue(),
      TopProperty(PropWeak(SeqConcat(BoolSeq("a"), BoolSeq("b")))));
}

// §F.5.3.2: w |=^- A completes w with the top tail T^omega; the open obligation
// a ##1 b is discharged by the tail, so a lone [a] satisfies weakly. The two-
// letter [a][b] satisfies outright, while a word that cannot even start the
// sequence is rejected however the tail is chosen.
TEST(FiniteWordSatisfaction, WeakCompletesWithTheTopTail) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(WeaklySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_TRUE(
      WeaklySatisfiesByFiniteWord(Word{L({"a"}), L({"b"})}, *BoolTrue(), *a));
  EXPECT_FALSE(WeaklySatisfiesByFiniteWord(Word{L({"x"})}, *BoolTrue(), *a));
}

// §F.5.3.2: w |=^+ A completes w with the bottom tail _|_^omega, which can
// never finish an open obligation. The completed [a][b] still matches, but a
// lone [a] is left unfinished and so does not satisfy strongly.
TEST(FiniteWordSatisfaction, StrongCompletesWithTheBottomTail) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(
      StronglySatisfiesByFiniteWord(Word{L({"a"}), L({"b"})}, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
}

// §F.5.3.2: a finite word that meets a strong obligation completely returns
// "Holds strongly" -- w |=^+ A.
TEST(FiniteWordSatisfaction, HoldsStronglyWhenStrongSatisfactionHolds) {
  auto a = InitialStrongAThenB();
  EXPECT_EQ(CheckFiniteWord(Word{L({"a"}), L({"b"})}, *BoolTrue(), *a),
            FiniteWordVerdict::kHoldsStrongly);
}

// §F.5.3.2: "Fails" when even the top-tail completion cannot satisfy the
// assertion -- not (w |=^- A).
TEST(FiniteWordSatisfaction, FailsWhenNotEvenWeaklySatisfied) {
  auto a = InitialStrongAThenB();
  EXPECT_EQ(CheckFiniteWord(Word{L({"x"})}, *BoolTrue(), *a),
            FiniteWordVerdict::kFails);
}

// §F.5.3.2: "Pending" when the top-tail completion satisfies the assertion but
// the word itself does not yet -- w |=^- A and not w |= A. A lone [a] leaves
// the strong obligation a ##1 b open: weak holds, neutral does not.
TEST(FiniteWordSatisfaction, PendingWhenWeakHoldsButNeutralDoesNot) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(WeaklySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWord(Word{L({"a"})}, *BoolTrue(), *a),
            FiniteWordVerdict::kPending);
}

// §F.5.3.2: "Holds (but does not hold strongly)" when the word neutrally
// satisfies the assertion yet the bottom-tail completion does not -- w |= A and
// not w |=^+ A. The weak obligation weak( a ##1 b ) is met by [a] under neutral
// satisfaction (it completes the sequence with T^omega internally), but the
// adversarial _|_^omega completion leaves it unmet.
TEST(FiniteWordSatisfaction, HoldsWithoutStrengthWhenNeutralButNotStrong) {
  auto a = InitialWeakAThenB();
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWord(Word{L({"a"})}, *BoolTrue(), *a),
            FiniteWordVerdict::kHolds);
}

// §F.5.3.2: the word may be empty. On the empty word the two completions still
// differ for initial @(1) strong(a ##1 b): the top tail makes the complement an
// all-_|_ word, so no enabling clock tick fires and weak satisfaction holds
// vacuously, while the bottom tail's complement does tick and leaves the strong
// obligation unmet, so strong satisfaction fails.
TEST(FiniteWordSatisfaction, WeakAndStrongDifferOnTheEmptyWord) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(WeaklySatisfiesByFiniteWord(Word{}, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(Word{}, *BoolTrue(), *a));
}

// §F.5.3.2: classifying the empty word. Weak holds and the empty word neutrally
// satisfies the assertion (no activation point fires), but strong does not, so
// the verdict is "Holds (but does not hold strongly)".
TEST(FiniteWordSatisfaction, EmptyWordHoldsWithoutStrength) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{}, *BoolTrue(), *a));
  EXPECT_FALSE(StronglySatisfiesByFiniteWord(Word{}, *BoolTrue(), *a));
  EXPECT_EQ(CheckFiniteWord(Word{}, *BoolTrue(), *a),
            FiniteWordVerdict::kHolds);
}

// §F.5.3.2: the labels a tool reports for each verdict.
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

// §F.5.3.2 reads the finite word through an infinite completion, so an always
// form has activation points in the tail as well as in w, and every point
// sees an infinite suffix. always @( 1 ) assert strong( a ##1 b ) on [a]: the
// word does not neutrally satisfy the statement, since its one activation
// sees the suffix [a], which no prefix of meets a ##1 b; but w T^omega gives
// that activation the suffix [a] T^omega, which meets it, and no letter of
// the top tail activates the statement, its complement being _|_, so the
// word satisfies the statement weakly, while w _|_^omega leaves the first
// activation unmet and the word does not satisfy it strongly. The verdict is
// therefore "Pending", where a reading that completed the word with a finite
// run of the tail would have found the last letter of every run unable to
// start a ##1 b and said "Fails".
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

// The word w followed by count copies of the tail letter: a finite prefix of
// the completion w T^omega or w _|_^omega.
Word Completed(const Word& word, const Letter& tail, std::size_t count) {
  Word out = word;
  for (std::size_t i = 0; i < count; ++i) {
    out.push_back(tail);
  }
  return out;
}

// The points of the bottom tail see the suffix _|_^omega, whose complement
// T^omega meets every sequence, and every one of them activates a statement,
// the complement T satisfying the clock and the enabling condition. initial
// @( 1 ) cover not strong( a ##1 b ) on the empty word: no letter activates
// it, and none of the top tail does, so the word neither neutrally nor weakly
// satisfies it; and every point of the bottom tail activates it and sees a
// suffix on which the negation fails, so the word does not satisfy it
// strongly either, and the verdict is "Fails" -- where a finite run of the
// tail has a last point whose one-letter suffix is too short to meet a ##1 b,
// on which the negation passes and the cover is met.
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

// The condition the subclause states for each verdict, in its own terms, on
// the cases above: "Holds strongly" is w |=^+ A, "Fails" is not w |=^- A,
// "Holds (but does not hold strongly)" is w |= A and not w |=^+ A, and
// "Pending" is w |=^- A and not w |= A.
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

// The family the agreement cases range over: for each of a strong and a weak
// sequence, a negation, an implication, a nexttime, an until, an accept_on
// abort and a disable iff guard, the four statements the constant clock gives
// it -- initial or always, assert or cover -- and one always assert under the
// clock clk.
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

// The words the agreement cases range over: the empty word, words that meet,
// start or miss the sequences, letters carrying the abort, disable and clock
// atoms, and the letters T and _|_ of Sigma themselves.
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

// §F.5.3.2 defines each relation by neutral satisfaction of the completed
// word, w |=^- A iff w T^omega |= A and w |=^+ A iff w _|_^omega |= A. The
// complement of the top tail is _|_, which satisfies no clock or enabling
// condition, so no point of that tail activates a statement and a finite run
// of it long enough for every body to have settled is read as the tail
// itself: on the family, weak satisfaction agrees with §F.5.3.1 asked about
// the word followed by such a run, and is true on some pair and false on
// another. The bottom tail activates at every point, so no finite run of it
// stands in for it, which the case above shows.
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

// The verdicts whose condition holds of a word and an assertion.
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

// The four conditions the subclause lists partition the pairs of a word and
// an assertion, since w |=^+ A implies w |= A, which implies w |=^- A, and
// the verdict CheckFiniteWord returns is the one whose condition holds. On
// the family, exactly one condition holds of every pair, it is the verdict's,
// and every verdict occurs.
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

// The enabling condition b of §F.5.3.1 reaches both relations through the
// completion. always @( 1 ) assert strong( a ) under b: on [x], which carries
// neither, no letter of the word or of the top tail activates the statement
// while every letter of the bottom tail does and fails it, so the word holds
// without holding strongly, where under the constant 1 the first letter
// activates and fails it and the word fails; and on [b] the letter activates
// and fails it under b as well.
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
