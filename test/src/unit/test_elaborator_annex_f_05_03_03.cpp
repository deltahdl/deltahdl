#include <gtest/gtest.h>

#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_vacuity.h"

using namespace delta;

namespace {

Letter L(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// A single-letter Boolean sequence matching the named atom.
auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// strong( name ): nonvacuous on every word (a §F.5.3.3 base case).
auto Strong(const std::string& name) { return PropStrong(Bs(name)); }

// ( name |-> strong( t ) ): a property whose non-vacuity depends on the word --
// it is nonvacuous exactly when the single-letter trigger `name` actually
// matches a prefix. Used to exercise the inductive rules that recurse into a
// word-sensitive operand.
auto Trig(const std::string& name) {
  return PropImplication(Bs(name), Strong("t"));
}

// §F.5.3.3 base: w |=^non strong(R) and w |=^non weak(R) hold for every w,
// including the empty word.
TEST(NonVacuity, StrongAndWeakAreAlwaysNonvacuous) {
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"a"})}, *Strong("a")));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{}, *Strong("a")));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"a"})}, *PropWeak(Bs("a"))));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{}, *PropWeak(Bs("a"))));
}

// §F.5.3.3: w |=^non ( P ) iff w |=^non P -- a parenthesis is transparent.
TEST(NonVacuity, ParenthesisIsTransparent) {
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"a"})}, *PropParen(Trig("a"))));
  EXPECT_FALSE(
      NonVacuouslyEvaluates(Word{L({"x"})}, *PropParen(Trig("a"))));
}

// §F.5.3.3: w |=^non R |-> P iff some prefix w^{0,i} tightly satisfies R and the
// matching suffix is nonvacuous for P. With a trigger that never matches, the
// implication is vacuous.
TEST(NonVacuity, ImplicationNeedsTheTriggerToMatch) {
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"a"})}, *Trig("a")));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *Trig("a")));
}

// §F.5.3.3: w |=^non ( P1 or P2 ) iff w |=^non P1 or w |=^non P2.
TEST(NonVacuity, DisjunctionIsNonvacuousWhenEitherSideIs) {
  auto p = PropOr(Trig("a"), Trig("a"));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *p));
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"x"})}, *PropOr(Trig("a"), Strong("s"))));
}

// §F.5.3.3: w |=^non ( P1 and P2 ) iff w |=^non P1 or w |=^non P2. A conjunction
// is nonvacuous when *either* conjunct is, even if the other is vacuous on w.
TEST(NonVacuity, ConjunctionIsNonvacuousWhenEitherSideIs) {
  auto vacuous_side = Trig("a");
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *vacuous_side));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"x"})},
                                    *PropAnd(Strong("s"), Trig("a"))));
}

// §F.5.3.3: w |=^non not P iff w-bar |=^non P. The complement turns a lone _|_
// (which leaves Trig("a") vacuous) into a T that matches the trigger.
TEST(NonVacuity, NegationEvaluatesOnTheComplement) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{LetterBottom()}, *Trig("a")));
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{LetterBottom()}, *PropNot(Trig("a"))));
}

// §F.5.3.3: w |=^non nexttime P iff |w| > 0 and w^{1.} |=^non P. The empty word
// is vacuous; a nonempty word defers to the suffix.
TEST(NonVacuity, NexttimeRequiresANonemptyWord) {
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"a"})}, *PropNexttime(Strong("b"))));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{}, *PropNexttime(Strong("b"))));
}

// §F.5.3.3: w |=^non ( P1 until P2 ) needs an index i where one operand is
// nonvacuous on the suffix. With operands that never become nonvacuous the until
// is vacuous; with an immediately nonvacuous operand at i = 0 it holds.
TEST(NonVacuity, UntilNeedsAnOperandToBecomeNonvacuous) {
  auto until = PropUntil(Trig("a"), Trig("a"));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *until));
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"a"})}, *PropUntil(Trig("a"), Trig("a"))));
}

// §F.5.3.3: the until witness may lie past index 0, which exercises the guard
// "for all 0 <= j < i, w^{j.} |= ( P1 and not P2 )". On [x][a] neither operand
// is nonvacuous at i = 0, but at i = 1 the suffix [a] matches the trigger while
// the guard holds vacuously across j = 0.
TEST(NonVacuity, UntilWitnessMayFollowANonvacuousGuardPrefix) {
  auto until = PropUntil(Trig("a"), Trig("a"));
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"x"}), L({"a"})}, *until));
}

// §F.5.3.3: w |=^non accept_on (b) P requires w |=^non P together with the abort
// condition. When no letter of w satisfies b, the first alternative holds, so
// the result follows the operand's non-vacuity.
TEST(NonVacuity, AcceptOnHoldsViaTheNoAbortAlternative) {
  auto p = PropAcceptOn(BoolAtom("b"), Strong("s"));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"s"})}, *p));
}

// §F.5.3.3: when the only letter satisfies b the no-abort alternative fails, so
// non-vacuity can hold only through the prefix alternative -- here the empty
// prefix completed with _|_^omega fails strong(s). The result is still true, and
// it can only come from that alternative since b is present.
TEST(NonVacuity, AcceptOnHoldsViaThePrefixAlternativeWhenBOccurs) {
  auto p = PropAcceptOn(BoolAtom("b"), Strong("s"));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"b", "s"})}, *p));
}

// §F.5.3.3: accept_on still requires its operand to be nonvacuous. With a
// vacuous operand the whole property is vacuous regardless of the abort
// condition.
TEST(NonVacuity, AcceptOnInheritsAVacuousOperand) {
  auto p = PropAcceptOn(BoolAtom("b"), Trig("a"));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *p));
}

// §F.5.3.3: the disable iff (b) P rule shares accept_on's shape and is evaluated
// over a top-level property. A bare top-level property defers to the property
// rule; the disable iff guard applies the abort shape; the no-abort alternative
// holds when b never occurs.
TEST(NonVacuity, DisableIffTopLevelUsesTheAbortShape) {
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevel(
      Word{L({"s"})}, *TopDisableIff(BoolAtom("b"), Strong("s"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesTopLevel(
      Word{L({"x"})}, *TopDisableIff(BoolAtom("b"), Trig("a"))));
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevel(Word{L({"a"})},
                                            *TopProperty(Trig("a"))));
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevel(
      Word{L({"a"})}, *TopParen(TopProperty(Trig("a")))));
}

// §F.5.3.3: "A word w satisfies property P nonvacuously iff w |= P and
// w |=^non P." A genuine match satisfies both relations.
TEST(NonVacuity, NonvacuousSatisfactionRequiresBothRelations) {
  EXPECT_TRUE(NeutrallySatisfies(Word{L({"s"})}, *Strong("s")));
  EXPECT_TRUE(SatisfiesNonVacuously(Word{L({"s"})}, *Strong("s")));
}

// §F.5.3.3: a vacuous pass -- the word neutrally satisfies the implication
// because its trigger never fires, yet the satisfaction is not nonvacuous, so
// the combined relation rejects it.
TEST(NonVacuity, NonvacuousSatisfactionRejectsAVacuousPass) {
  EXPECT_TRUE(NeutrallySatisfies(Word{L({"x"})}, *Trig("a")));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *Trig("a")));
  EXPECT_FALSE(SatisfiesNonVacuously(Word{L({"x"})}, *Trig("a")));
}

// §F.5.3.3: the same combined test at the top level pairs neutral satisfaction
// with non-vacuity of the top-level property.
TEST(NonVacuity, TopLevelNonvacuousSatisfactionCombinesBothRelations) {
  auto top = TopProperty(Trig("a"));
  EXPECT_FALSE(SatisfiesTopLevelNonVacuously(Word{L({"x"})}, *top));
  EXPECT_TRUE(SatisfiesTopLevelNonVacuously(Word{L({"s"})},
                                            *TopProperty(Strong("s"))));
}

// §F.5.3.3 edge case: R |-> P needs an index 0 <= i with w^{0,i} |= R, so on the
// empty word there is no such index and the implication is vacuous.
TEST(NonVacuity, ImplicationIsVacuousOnTheEmptyWord) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{}, *Trig("a")));
}

// §F.5.3.3 edge case: P1 until P2 needs an index 0 <= i < |w| witnessing one
// operand's non-vacuity, so the empty word makes the until vacuous.
TEST(NonVacuity, UntilIsVacuousOnTheEmptyWord) {
  EXPECT_FALSE(
      NonVacuouslyEvaluates(Word{}, *PropUntil(Trig("a"), Trig("a"))));
}

// §F.5.3.3: the conjunction rule is "either side nonvacuous", so when both
// conjuncts are vacuous on the word the conjunction is vacuous too -- the
// complementary branch to ConjunctionIsNonvacuousWhenEitherSideIs.
TEST(NonVacuity, ConjunctionIsVacuousWhenBothSidesAre) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})},
                                     *PropAnd(Trig("a"), Trig("a"))));
}

// §F.5.3.3: nexttime is not merely a length gate -- past the |w| > 0 check it
// defers to non-vacuity of the suffix. Here the one-letter suffix is empty after
// the shift, leaving the trigger property vacuous, so nexttime is vacuous even
// though the word is nonempty.
TEST(NonVacuity, NexttimeDefersToTheSuffixNonVacuity) {
  EXPECT_FALSE(
      NonVacuouslyEvaluates(Word{L({"a"})}, *PropNexttime(Trig("a"))));
}

// §F.5.3.3 edge case: on the empty word no letter can satisfy the abort
// condition b, so accept_on's no-abort alternative holds and the result reduces
// to the operand's non-vacuity -- nonvacuous for strong(s), vacuous for a
// trigger that cannot match.
TEST(NonVacuity, AcceptOnOnTheEmptyWordFollowsTheOperand) {
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{},
                                    *PropAcceptOn(BoolAtom("b"), Strong("s"))));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{},
                                     *PropAcceptOn(BoolAtom("b"), Trig("a"))));
}

// §F.5.3.3 edge case: the disable iff top-level rule shares accept_on's shape, so
// on the empty word it likewise reduces to the operand's non-vacuity.
TEST(NonVacuity, DisableIffOnTheEmptyWordFollowsTheOperand) {
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevel(
      Word{}, *TopDisableIff(BoolAtom("b"), Strong("s"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesTopLevel(
      Word{}, *TopDisableIff(BoolAtom("b"), Trig("a"))));
}

}  // namespace
