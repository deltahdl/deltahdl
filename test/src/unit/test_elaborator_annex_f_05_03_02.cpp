#include <gtest/gtest.h>

#include <set>
#include <string>

#include "elaborator/annex_f_finite_word_satisfaction.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter L(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto BoolSeq(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// initial @( 1 ) strong( a ##1 b ): a single activation at index 0 whose body is
// the strong sequence a then b. Under T^p(., 1) the constant clock collapses, so
// the body holds exactly when a ##1 b is tightly matched within the word.
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
  EXPECT_TRUE(
      WeaklySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_TRUE(WeaklySatisfiesByFiniteWord(Word{L({"a"}), L({"b"})},
                                          *BoolTrue(), *a));
  EXPECT_FALSE(
      WeaklySatisfiesByFiniteWord(Word{L({"x"})}, *BoolTrue(), *a));
}

// §F.5.3.2: w |=^+ A completes w with the bottom tail _|_^omega, which can never
// finish an open obligation. The completed [a][b] still matches, but a lone [a]
// is left unfinished and so does not satisfy strongly.
TEST(FiniteWordSatisfaction, StrongCompletesWithTheBottomTail) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(StronglySatisfiesByFiniteWord(Word{L({"a"}), L({"b"})},
                                            *BoolTrue(), *a));
  EXPECT_FALSE(
      StronglySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
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
// the word itself does not yet -- w |=^- A and not w |= A. A lone [a] leaves the
// strong obligation a ##1 b open: weak holds, neutral does not.
TEST(FiniteWordSatisfaction, PendingWhenWeakHoldsButNeutralDoesNot) {
  auto a = InitialStrongAThenB();
  EXPECT_TRUE(
      WeaklySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{L({"a"})}, *BoolTrue(), *a));
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
  EXPECT_FALSE(
      StronglySatisfiesByFiniteWord(Word{L({"a"})}, *BoolTrue(), *a));
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

}  // namespace
