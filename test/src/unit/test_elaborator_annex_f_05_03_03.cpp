#include <gtest/gtest.h>

#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_derived_forms.h"
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
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"a"})}, *PropParen(Trig("a"))));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *PropParen(Trig("a"))));
}

// §F.5.3.3: w |=^non R |-> P iff some prefix w^{0,i} tightly satisfies R and
// the matching suffix is nonvacuous for P. With a trigger that never matches,
// the implication is vacuous.
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

// §F.5.3.3: w |=^non ( P1 and P2 ) iff w |=^non P1 or w |=^non P2. A
// conjunction is nonvacuous when *either* conjunct is, even if the other is
// vacuous on w.
TEST(NonVacuity, ConjunctionIsNonvacuousWhenEitherSideIs) {
  auto vacuous_side = Trig("a");
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *vacuous_side));
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"x"})}, *PropAnd(Strong("s"), Trig("a"))));
}

// §F.5.3.3: w |=^non not P iff w-bar |=^non P. The complement turns a lone _|_
// (which leaves Trig("a") vacuous) into a T that matches the trigger.
TEST(NonVacuity, NegationEvaluatesOnTheComplement) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{LetterBottom()}, *Trig("a")));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{LetterBottom()}, *PropNot(Trig("a"))));
}

// §F.5.3.3: w |=^non nexttime P iff |w| > 0 and w^{1.} |=^non P. The empty word
// is vacuous; a nonempty word defers to the suffix.
TEST(NonVacuity, NexttimeRequiresANonemptyWord) {
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"a"})}, *PropNexttime(Strong("b"))));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{}, *PropNexttime(Strong("b"))));
}

// §F.5.3.3: w |=^non ( P1 until P2 ) needs an index i where one operand is
// nonvacuous on the suffix. With operands that never become nonvacuous the
// until is vacuous; with an immediately nonvacuous operand at i = 0 it holds.
TEST(NonVacuity, UntilNeedsAnOperandToBecomeNonvacuous) {
  auto until = PropUntil(Trig("a"), Trig("a"));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *until));
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{L({"a"})}, *PropUntil(Trig("a"), Trig("a"))));
}

// §F.5.3.3: the until witness may lie past index 0, which exercises the guard
// "for all 0 <= j < i, w^{j.} |= ( P1 and not P2 )". With P2 the negation of
// P1, the guard is P1 twice over. On [x][a] neither operand is nonvacuous at
// i = 0, since the trigger matches no prefix there and the §F.5.3.1 complement
// leaves an atom letter as it is, but at i = 1 the suffix [a] matches the
// trigger while the guard holds vacuously across j = 0. The same operand on
// both sides would make the guard a contradiction and hide the witness.
TEST(NonVacuity, UntilWitnessMayFollowANonvacuousGuardPrefix) {
  auto until = PropUntil(Trig("a"), PropNot(Trig("a")));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"x"}), L({"a"})}, *until));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"}), L({"a"})},
                                     *PropUntil(Trig("a"), Trig("a"))));
}

// §F.5.3.3: w |=^non accept_on (b) P requires w |=^non P together with the
// abort condition. When no letter of w satisfies b, the first alternative
// holds, so the result follows the operand's non-vacuity.
TEST(NonVacuity, AcceptOnHoldsViaTheNoAbortAlternative) {
  auto p = PropAcceptOn(BoolAtom("b"), Strong("s"));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"s"})}, *p));
}

// §F.5.3.3: when a letter satisfies b the no-abort alternative fails, so
// non-vacuity can hold only through the prefix alternative: some prefix x free
// of b settles P, x _|_^omega meeting it or x T^omega not meeting it. On
// [s][b] the prefix [s] completed with _|_^omega meets strong(s); on [x][b]
// the prefix [x] completed with T^omega does not meet it, no prefix of that
// completion being the one letter s; and on [b,s] the only b-free prefix is
// the empty one, whose bottom completion does not meet strong(s) and whose
// top completion does, so the evaluation is vacuous -- which reading the
// bottom completion as settling P by failing it would have got wrong.
TEST(NonVacuity, AcceptOnHoldsViaThePrefixAlternativeWhenBOccurs) {
  auto p = PropAcceptOn(BoolAtom("b"), Strong("s"));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"s"}), L({"b"})}, *p));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"x"}), L({"b"})}, *p));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"b", "s"})}, *p));
}

// §F.5.3.3: accept_on still requires its operand to be nonvacuous. With a
// vacuous operand the whole property is vacuous regardless of the abort
// condition.
TEST(NonVacuity, AcceptOnInheritsAVacuousOperand) {
  auto p = PropAcceptOn(BoolAtom("b"), Trig("a"));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"x"})}, *p));
}

// §F.5.3.3: the disable iff (b) P rule shares accept_on's shape and is
// evaluated over a top-level property. A bare top-level property defers to the
// property rule; the disable iff guard applies the abort shape; the no-abort
// alternative holds when b never occurs.
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
  EXPECT_TRUE(
      SatisfiesTopLevelNonVacuously(Word{L({"s"})}, *TopProperty(Strong("s"))));
}

// §F.5.3.3 edge case: R |-> P needs an index 0 <= i with w^{0,i} |= R, so on
// the empty word there is no such index and the implication is vacuous.
TEST(NonVacuity, ImplicationIsVacuousOnTheEmptyWord) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{}, *Trig("a")));
}

// §F.5.3.3 edge case: P1 until P2 needs an index 0 <= i < |w| witnessing one
// operand's non-vacuity, so the empty word makes the until vacuous.
TEST(NonVacuity, UntilIsVacuousOnTheEmptyWord) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{}, *PropUntil(Trig("a"), Trig("a"))));
}

// §F.5.3.3: the conjunction rule is "either side nonvacuous", so when both
// conjuncts are vacuous on the word the conjunction is vacuous too -- the
// complementary branch to ConjunctionIsNonvacuousWhenEitherSideIs.
TEST(NonVacuity, ConjunctionIsVacuousWhenBothSidesAre) {
  EXPECT_FALSE(
      NonVacuouslyEvaluates(Word{L({"x"})}, *PropAnd(Trig("a"), Trig("a"))));
}

// §F.5.3.3: nexttime is not merely a length gate -- past the |w| > 0 check it
// defers to non-vacuity of the suffix. Here the one-letter suffix is empty
// after the shift, leaving the trigger property vacuous, so nexttime is vacuous
// even though the word is nonempty.
TEST(NonVacuity, NexttimeDefersToTheSuffixNonVacuity) {
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"a"})}, *PropNexttime(Trig("a"))));
}

// §F.5.3.3 edge case: on the empty word no letter can satisfy the abort
// condition b, so accept_on's no-abort alternative holds and the result reduces
// to the operand's non-vacuity -- nonvacuous for strong(s), vacuous for a
// trigger that cannot match.
TEST(NonVacuity, AcceptOnOnTheEmptyWordFollowsTheOperand) {
  EXPECT_TRUE(
      NonVacuouslyEvaluates(Word{}, *PropAcceptOn(BoolAtom("b"), Strong("s"))));
  EXPECT_FALSE(
      NonVacuouslyEvaluates(Word{}, *PropAcceptOn(BoolAtom("b"), Trig("a"))));
}

// §F.5.3.3 edge case: the disable iff top-level rule shares accept_on's shape,
// so on the empty word it likewise reduces to the operand's non-vacuity.
TEST(NonVacuity, DisableIffOnTheEmptyWordFollowsTheOperand) {
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevel(
      Word{}, *TopDisableIff(BoolAtom("b"), Strong("s"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesTopLevel(
      Word{}, *TopDisableIff(BoolAtom("b"), Trig("a"))));
}

// The derived operators §F.5.3.3 states a rule for. Each rule is over the
// operands, and where it parts from the unfolding of §F.3.4.3 the cases show
// both, the unfolding through NonVacuouslyEvaluates on the unfolded form.

// §F.5.3.3: ( P1 iff P2 ) is nonvacuous iff either operand is. On the
// letter _|_ neither trigger matches, so the stated rule says vacuous, where
// the unfolding into implications is nonvacuous through the negation that
// turns _|_ into the T both triggers match.
TEST(NonVacuity, IffIsNonvacuousWhenEitherSideIs) {
  auto p1 = Trig("a");
  auto p2 = Trig("b");
  EXPECT_TRUE(NonVacuouslyEvaluatesIff(Word{L({"a"})}, *p1, *p2));
  EXPECT_TRUE(NonVacuouslyEvaluatesIff(Word{L({"b"})}, *p1, *p2));
  EXPECT_FALSE(NonVacuouslyEvaluatesIff(Word{L({"x"})}, *p1, *p2));
  EXPECT_FALSE(NonVacuouslyEvaluatesIff(Word{LetterBottom()}, *p1, *p2));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{LetterBottom()}, *PropIff(p1, p2)));
}

// §F.5.3.3: ( P1 implies P2 ) is nonvacuous iff P1 holds and is nonvacuous
// and P2 is nonvacuous. On [a,t] the trigger of P1 matches and its strong(t)
// is met; on [a] the trigger matches but P1 fails; on [x] P1 holds only
// vacuously, which the stated rule rejects where the unfolding ( not P1 or
// P2 ) accepts through the nonvacuous strong(s); and a vacuous consequent is
// rejected too.
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

// §F.5.3.3: ( P1 s_until P2 ) has the rule of ( P1 until P2 ), witness past
// index 0 included.
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

// §F.5.3.3: ( always P ) is nonvacuous iff some letter is one from which P
// is nonvacuous and before which P holds. always Trig(a) on [x][a,t]: the
// trigger matches from the second letter, and from the first P holds
// vacuously, so the witness stands; on [x][x] there is none, nor on the
// empty word. always ( not Trig(a) ) on the same [x][a,t]: from the second
// letter the negation is nonvacuous, but from the first it fails, since
// Trig(a) holds there, so the stated rule says vacuous -- where the
// unfolding ( P until 0 ) is nonvacuous from its first letter, strong(0)
// being a base case.
TEST(NonVacuity, AlwaysNeedsAWitnessBeforeWhichPHolds) {
  const Word kXAt{L({"x"}), L({"a", "t"})};
  EXPECT_TRUE(NonVacuouslyEvaluatesAlways(kXAt, *Trig("a")));
  EXPECT_FALSE(
      NonVacuouslyEvaluatesAlways(Word{L({"x"}), L({"x"})}, *Trig("a")));
  EXPECT_FALSE(NonVacuouslyEvaluatesAlways(Word{}, *Trig("a")));
  EXPECT_FALSE(NonVacuouslyEvaluatesAlways(kXAt, *PropNot(Trig("a"))));
  EXPECT_TRUE(NonVacuouslyEvaluates(kXAt, *PropAlways(PropNot(Trig("a")))));
}

// §F.5.3.3: ( always [m:n] P ) and ( s_always [m:n] P ) take their witness
// from m through n and their guard from m, and n alone bounds the witness,
// w^{i.} being the empty word past |w|. always [0:0] Trig(a) on [x][a,t] has
// no witness where always [1:1] and always [1:2] do; always [0:1] of the
// negation fails its guard at index 0 where always [1:1] has no guard to
// fail; and always [3:4] strong(s) on [x][x] is nonvacuous from the empty
// suffix, as strong is on every word, where Trig(a) is not.
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

// §F.5.3.3: ( s_eventually P ) is nonvacuous iff some letter is one from
// which P is nonvacuous and before which not P holds. s_eventually
// ( not Trig(a) ) on [x][a,t]: from the second letter the negation is
// nonvacuous and from the first not not Trig(a), that is Trig(a), holds, so
// the witness stands; s_eventually Trig(a) on the same word has its witness
// at the second letter but Trig(a) holds from the first, so not P does not,
// and the stated rule says vacuous -- where the unfolding
// ( not always not P ) is nonvacuous through the strong(0) of its always.
TEST(NonVacuity, SEventuallyNeedsPToFailBeforeItsWitness) {
  const Word kXAt{L({"x"}), L({"a", "t"})};
  EXPECT_TRUE(NonVacuouslyEvaluatesSEventually(kXAt, *PropNot(Trig("a"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesSEventually(kXAt, *Trig("a")));
  EXPECT_TRUE(NonVacuouslyEvaluates(kXAt, *PropSEventually(Trig("a"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesSEventually(Word{L({"x"}), L({"x"})},
                                                *PropNot(Trig("a"))));
  EXPECT_FALSE(NonVacuouslyEvaluatesSEventually(Word{}, *PropNot(Trig("a"))));
}

// §F.5.3.3: ( eventually [m:n] P ) and ( s_eventually [m:n] P ) take their
// witness from m through n and their guard from m. eventually [1:1] of the
// negation on [x][a,t] has its witness and no guard, eventually [0:1] has
// the guard hold at index 0, eventually [0:0] has no witness; and
// eventually [0:1] Trig(a) fails its guard where eventually [1:1] has none.
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

// §F.5.3.3: ( reject_on (b) P ) has the abort shape of accept_on: on [x] no
// letter satisfies b; on [s][b] the prefix [s] settles strong(s) under
// _|_^omega; on [b,s] the empty prefix settles nothing. On the letter T,
// which satisfies b, the empty prefix settles nothing either, so the stated
// rule says vacuous, where the unfolding ( not accept_on (b) not P ) is
// nonvacuous, its negation turning the T into a _|_ that satisfies no b.
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

// §F.5.3.3 closes that the relation is not stated for every derived operator
// and is then defined by unrolling the derivation. ( s_nexttime P ) is
// ( not nexttime not P ), and unrolling gives |w| > 0 and w^{1.} |=^non P:
// nonvacuous on [x][a,t], where the second letter matches the trigger, and
// not on [a,t][x] or on the empty word.
TEST(NonVacuity, TheOtherDerivedOperatorsUnroll) {
  auto p = PropSNexttime(Trig("a"));
  EXPECT_TRUE(NonVacuouslyEvaluates(Word{L({"x"}), L({"a", "t"})}, *p));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{L({"a", "t"}), L({"x"})}, *p));
  EXPECT_FALSE(NonVacuouslyEvaluates(Word{}, *p));
}

}  // namespace
