#include <gtest/gtest.h>

#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto BoolSeq(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// §F.5.3.1: w |= strong(R) iff there exists 0 <= j < |w| with w^{0,j} |= R. For
// R = (a ##1 b), the witness prefix is the two-letter [a][b]; an extra trailing
// letter still satisfies because some prefix matches.
TEST(NeutralSatisfaction, StrongHoldsWhenSomePrefixTightlyMatches) {
  auto p = PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *p));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"}), A({"c"})}, *p));
  // No prefix completes the sequence, so strong fails.
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"}), A({"b"})}, *p));
}

// §F.5.3.1: w |= weak(R) iff for every 0 <= j < |w|, w^{0,j} T^omega |=
// strong(R). For R = (a ##1 b) a lone [a] passes weakly -- the T-completion can
// still finish the sequence -- where strong would fail.
TEST(NeutralSatisfaction, WeakAcceptsAnUnfinishedSequenceStrongRejects) {
  auto strong = PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b")));
  auto weak = PropWeak(SeqConcat(BoolSeq("a"), BoolSeq("b")));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *strong));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *weak));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *weak));
  // A first letter that cannot even start the sequence fails weakly too.
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"})}, *weak));
}

// §F.5.3.1: w |= ( P ) iff w |= P -- parentheses are transparent.
TEST(NeutralSatisfaction, ParenthesisIsTransparent) {
  auto p = PropParen(PropStrong(BoolSeq("a")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"})}, *p));
}

// §F.5.3.1: w |= not P iff w-bar |= P. The complement only swaps the T and _|_
// letters, so it flips a strong(a) verdict between the top and bottom letters.
TEST(NeutralSatisfaction, NotEvaluatesAgainstTheComplementWord) {
  auto strong = PropStrong(BoolSeq("a"));
  auto negated = PropNot(PropStrong(BoolSeq("a")));
  EXPECT_TRUE(NeutrallySatisfies(Word{LetterTop()}, *strong));
  EXPECT_FALSE(NeutrallySatisfies(Word{LetterTop()}, *negated));
  EXPECT_TRUE(NeutrallySatisfies(Word{LetterBottom()}, *negated));
}

// §F.5.3.1: w |= ( R |-> P ) iff for every 0 <= j < |w| with w-bar^{0,j} |= R,
// w^{j.} |= P. With R = a, the obligation triggers at index 0 and requires the
// consequent there.
TEST(NeutralSatisfaction, ImplicationDischargesConsequentAtEachMatch) {
  auto impl = PropImplication(BoolSeq("a"), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a", "b"})}, *impl));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *impl));
  // The antecedent never matches, so the implication holds vacuously.
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"})}, *impl));
}

// §F.5.3.1: w |= ( P1 or P2 ) iff w |= P1 or w |= P2.
TEST(NeutralSatisfaction, OrTakesEitherOperand) {
  auto p = PropOr(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *p));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"b"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"})}, *p));
}

// §F.5.3.1: w |= ( P1 and P2 ) iff w |= P1 and w |= P2.
TEST(NeutralSatisfaction, AndRequiresBothOperands) {
  auto p = PropAnd(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a", "b"})}, *p));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *p));
}

// §F.5.3.1: w |= ( nexttime P ) iff |w| = 0 or w^{1.} |= P. The property is
// evaluated on the word with its first letter removed.
TEST(NeutralSatisfaction, NexttimeShiftsPastTheFirstLetter) {
  auto p = PropNexttime(PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *p));
  // The shifted word is empty, so strong(b) cannot hold.
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *p));
}

// §F.5.3.1: w |= ( P1 until P2 ) iff some suffix satisfies P2 with every earlier
// suffix satisfying P1, or every suffix satisfies P1.
TEST(NeutralSatisfaction, UntilHoldsUntilTheReleasingSuffix) {
  auto p = PropUntil(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(
      NeutrallySatisfies(Word{A({"a"}), A({"a"}), A({"b"})}, *p));
  // No suffix releases with b and not every suffix satisfies a.
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"x"})}, *p));
}

// §F.5.3.1: w |= ( accept_on (b) P ) iff w |= P, or for some 0 <= i < |w| with
// w^i |= b, w^{0,i-1} T^omega |= P. The abort lets the T-completion satisfy P
// even when the raw word does not.
TEST(NeutralSatisfaction, AcceptOnPassesOnAbortCompletion) {
  auto p = PropAcceptOn(BoolAtom("r"), PropStrong(BoolSeq("c")));
  // First disjunct: the word satisfies P directly.
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"c"})}, *p));
  // Second disjunct: P fails on the word, but the abort at r yields a passing
  // T^omega completion.
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"r"})}, *p));
  // Neither P nor an abort condition holds.
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"})}, *p));
}

// §F.5.3.1: for T = P, w |= T iff w |= P.
TEST(NeutralSatisfaction, TopLevelBarePropertyDefersToTheProperty) {
  auto t = TopProperty(PropStrong(BoolSeq("a")));
  EXPECT_TRUE(NeutrallySatisfiesTopLevel(Word{A({"a"})}, *t));
  EXPECT_FALSE(NeutrallySatisfiesTopLevel(Word{A({"x"})}, *t));
}

// §F.5.3.1: for T = disable iff (b) P, w |= T iff either w |= P with no letter
// of w satisfying b, or some letter satisfies b and w^{0,i-1} _|_^omega |= P
// for i the least index with w^i |= b.
TEST(NeutralSatisfaction, TopLevelDisableIffSatisfaction) {
  auto t = TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a")));
  // No disable: behaves like the guarded property.
  EXPECT_TRUE(NeutrallySatisfiesTopLevel(Word{A({"a"})}, *t));
  // Disable at index 0: the _|_^omega completion cannot satisfy strong(a).
  EXPECT_FALSE(NeutrallySatisfiesTopLevel(Word{A({"d"})}, *t));
  // Disable at index 1: the prefix already carries an 'a', so the completion
  // satisfies strong(a).
  EXPECT_TRUE(NeutrallySatisfiesTopLevel(Word{A({"a"}), A({"d"})}, *t));
}

// §F.5.3.1: w |= ( T ) iff w |= T.
TEST(NeutralSatisfaction, TopLevelParenthesisIsTransparent) {
  auto t = TopParen(TopProperty(PropStrong(BoolSeq("a"))));
  EXPECT_TRUE(NeutrallySatisfiesTopLevel(Word{A({"a"})}, *t));
  EXPECT_FALSE(NeutrallySatisfiesTopLevel(Word{A({"x"})}, *t));
}

// §F.5.3.1: for T = P, w |/=^d T -- a bare property is never disabled.
TEST(Disabling, BarePropertyIsNeverDisabled) {
  auto t = TopProperty(PropStrong(BoolSeq("a")));
  EXPECT_FALSE(DisablesTopLevel(Word{A({"a"})}, *t));
  EXPECT_FALSE(DisablesTopLevel(Word{A({"x"})}, *t));
}

// §F.5.3.1: for T = disable iff (b) P, w |=^d T iff some letter satisfies b and
// both w^{0,i-1} T^omega |= P and w^{0,i-1} _|_^omega |/= P for i the least
// index with w^i |= b.
TEST(Disabling, DisableIffIsDisabledWhenCompletionsDiverge) {
  auto t = TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a")));
  // d at index 0: empty prefix. T^omega satisfies strong(a); _|_^omega does
  // not. The verdict diverges, so T is disabled.
  EXPECT_TRUE(DisablesTopLevel(Word{A({"d"})}, *t));
  // No letter satisfies d, so the disabling condition cannot fire.
  EXPECT_FALSE(DisablesTopLevel(Word{A({"a"})}, *t));
}

// §F.5.3.1: w |=^d ( T ) iff w |=^d T.
TEST(Disabling, ParenthesizedTopLevelPropagatesDisabling) {
  auto t = TopParen(TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a"))));
  EXPECT_TRUE(DisablesTopLevel(Word{A({"d"})}, *t));
}

// §F.5.3.1: "T is said to pass on w if w |= T", "is disabled if w |=^d T", and
// "fails if T neither passes nor is disabled." Pass and disabled are mutually
// exclusive.
TEST(Disabling, PassDisabledFailTrichotomy) {
  auto bare = TopProperty(PropStrong(BoolSeq("a")));
  // Passes: satisfied and (being a bare property) not disabled.
  EXPECT_TRUE(PassesTopLevel(Word{A({"a"})}, *bare));
  EXPECT_FALSE(IsDisabledTopLevel(Word{A({"a"})}, *bare));
  EXPECT_FALSE(FailsTopLevel(Word{A({"a"})}, *bare));

  // Fails: neither satisfied nor disabled.
  EXPECT_FALSE(PassesTopLevel(Word{A({"x"})}, *bare));
  EXPECT_FALSE(IsDisabledTopLevel(Word{A({"x"})}, *bare));
  EXPECT_TRUE(FailsTopLevel(Word{A({"x"})}, *bare));

  // Disabled: disabled and therefore neither pass nor fail.
  auto guarded = TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a")));
  EXPECT_FALSE(PassesTopLevel(Word{A({"d"})}, *guarded));
  EXPECT_TRUE(IsDisabledTopLevel(Word{A({"d"})}, *guarded));
  EXPECT_FALSE(FailsTopLevel(Word{A({"d"})}, *guarded));
}

// Edge of §F.5.3.1: w |= ( nexttime P ) iff |w| = 0 or w^{1.} |= P. The empty
// word takes the first disjunct, so nexttime holds regardless of P.
TEST(NeutralSatisfaction, NexttimeHoldsVacuouslyOnTheEmptyWord) {
  auto p = PropNexttime(PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{}, *p));
}

// Edge of §F.5.3.1: the second disjunct of ( P1 until P2 ) -- when no suffix
// releases with P2, the property still holds if every suffix satisfies P1.
TEST(NeutralSatisfaction, UntilHoldsWhenLeftOperandHoldsThroughout) {
  auto p = PropUntil(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"a"})}, *p));
}

// Edge of §F.5.3.1: w |= not P uses the complement w-bar, which leaves letters
// in 2^P untouched -- so over atom-only words negation tracks the underlying
// property rather than flipping it (the flip is exclusive to T and _|_).
TEST(NeutralSatisfaction, NotLeavesAtomLettersUnchanged) {
  auto negated = PropNot(PropStrong(BoolSeq("a")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *negated));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"})}, *negated));
}

// Edge of §F.5.3.1: ( R |-> P ) with a two-letter antecedent matches at index
// 1, and the consequent is then evaluated on the overlap suffix w^{1.}.
TEST(NeutralSatisfaction, ImplicationEvaluatesConsequentOnTheOverlapSuffix) {
  auto impl = PropImplication(SeqConcat(BoolSeq("a"), BoolSeq("b")),
                              PropStrong(SeqConcat(BoolSeq("b"), BoolSeq("c"))));
  // Antecedent (a ##1 b) matches [a][b]; consequent strong(b ##1 c) holds on
  // the suffix [b][c].
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"}), A({"c"})}, *impl));
  // Same antecedent match, but the suffix no longer satisfies the consequent.
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"b"}), A({"x"})}, *impl));
}

// Edge of §F.5.3.1: the abort of ( accept_on (b) P ) can fire at a later index,
// completing a nonempty prefix with T^omega so an unfinished sequence passes.
TEST(NeutralSatisfaction, AcceptOnCompletesNonemptyPrefixAtLaterAbort) {
  auto p =
      PropAcceptOn(BoolAtom("r"), PropStrong(SeqConcat(BoolSeq("a"),
                                                       BoolSeq("b"))));
  // strong(a ##1 b) fails on [a][r], but the abort at index 1 completes the
  // prefix [a] with T^omega, which finishes the sequence.
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"r"})}, *p));
}

// Edge of §F.5.3.1: the first bullet of T = disable iff (b) P requires w |= P
// when no letter satisfies b -- a failing property without any disable fails.
TEST(NeutralSatisfaction, DisableIffFailsWhenPropertyFailsAndNothingDisables) {
  auto t = TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a")));
  EXPECT_FALSE(NeutrallySatisfiesTopLevel(Word{A({"x"})}, *t));
}

// Edge of §F.5.3.1: disable iff is disabled only when the T^omega and _|_^omega
// completions disagree. When the prefix already decides P both completions
// agree, so the property is not disabled -- here it passes instead.
TEST(Disabling, DisableIffNotDisabledWhenCompletionsAgree) {
  auto t = TopDisableIff(BoolAtom("d"), PropStrong(BoolSeq("a")));
  // d first fires at index 1, but the prefix [a] already satisfies strong(a)
  // under either completion, so the verdicts agree.
  EXPECT_FALSE(DisablesTopLevel(Word{A({"a"}), A({"d"})}, *t));
  EXPECT_TRUE(PassesTopLevel(Word{A({"a"}), A({"d"})}, *t));
}

}  // namespace
