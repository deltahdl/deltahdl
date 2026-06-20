#include <gtest/gtest.h>

#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto BoolSeq(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// A clocked property @( clk ) strong( a ): the Boolean a sampled on clk. Under
// T^p(., 1) it expands to strong(!clk [*0:$] ##1 (clk & a)), so it holds
// exactly when a is true at the first clk tick.
auto ClockedStrongA() {
  return ClkClock(BoolAtom("clk"), ClkStrong(SeqBoolean(BoolAtom("a"))));
}

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

// §F.5.3.1: w |= ( P1 until P2 ) iff some suffix satisfies P2 with every
// earlier suffix satisfying P1, or every suffix satisfies P1.
TEST(NeutralSatisfaction, UntilHoldsUntilTheReleasingSuffix) {
  auto p = PropUntil(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"a"}), A({"b"})}, *p));
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
  auto impl =
      PropImplication(SeqConcat(BoolSeq("a"), BoolSeq("b")),
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
  auto p = PropAcceptOn(BoolAtom("r"),
                        PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b"))));
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

// §F.5.3.1: w |= Q iff w |= T^p(Q, 1). For Q = @(clk) strong(a), sampling on a
// word that ticks clk every letter behaves like the unclocked strong(a).
TEST(ClockedProperty, SatisfiedWhenSampledBooleanHoldsAtClockTick) {
  auto q = ClockedStrongA();
  // clk and a coincide at index 0: the sampled sequence completes.
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(Word{A({"clk", "a"})}, *q));
  // A clk tick without a fails: the sampled Boolean is false where it is read.
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(Word{A({"clk"})}, *q));
  // No clk tick at all: there is no sampling point, so strong cannot complete.
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(Word{A({"a"})}, *q));
}

// §F.5.3.1: w |= Q iff w |= T^p(Q, 1). The clock idles until its first tick, so
// the sampled obligation waits for the clk-carrying letter.
TEST(ClockedProperty, ClockIdlesUntilItsFirstTick) {
  auto q = ClockedStrongA();
  // clk first ticks at index 1, where a also holds: satisfied.
  EXPECT_TRUE(
      NeutrallySatisfiesClockedProperty(Word{A({"x"}), A({"clk", "a"})}, *q));
  // clk ticks at index 1 but a is absent there: not satisfied.
  EXPECT_FALSE(
      NeutrallySatisfiesClockedProperty(Word{A({"x"}), A({"clk"})}, *q));
}

// §F.5.3.1: for U = Q, w |= U iff w |= Q.
TEST(ClockedTopLevel, BarePropertyDefersToTheClockedProperty) {
  auto u = ClockedTopProperty(ClockedStrongA());
  EXPECT_TRUE(NeutrallySatisfiesTopLevelClocked(Word{A({"clk", "a"})}, *u));
  EXPECT_FALSE(NeutrallySatisfiesTopLevelClocked(Word{A({"clk"})}, *u));
}

// §F.5.3.1: for U = disable iff (b) Q, w |= U mirrors the T rule with Q for P.
TEST(ClockedTopLevel, DisableIffSatisfaction) {
  auto u = ClockedTopDisableIff(BoolAtom("d"), ClockedStrongA());
  // No disable: behaves like the guarded clocked property.
  EXPECT_TRUE(NeutrallySatisfiesTopLevelClocked(Word{A({"clk", "a"})}, *u));
  // Disable at index 0: the _|_^omega completion cannot satisfy the sampled
  // sequence, since _|_ models no Boolean.
  EXPECT_FALSE(NeutrallySatisfiesTopLevelClocked(Word{A({"d"})}, *u));
}

// §F.5.3.1: w |= ( U ) iff w |= U.
TEST(ClockedTopLevel, ParenthesisIsTransparent) {
  auto u = ClockedTopParen(ClockedTopProperty(ClockedStrongA()));
  EXPECT_TRUE(NeutrallySatisfiesTopLevelClocked(Word{A({"clk", "a"})}, *u));
  EXPECT_FALSE(NeutrallySatisfiesTopLevelClocked(Word{A({"clk"})}, *u));
}

// §F.5.3.1: for U = disable iff (b) Q, w |=^d U holds when the T^omega and
// _|_^omega completions of the prefix diverge.
TEST(ClockedTopLevel, DisableIffIsDisabledWhenCompletionsDiverge) {
  auto u = ClockedTopDisableIff(BoolAtom("d"), ClockedStrongA());
  // d at index 0: T^omega satisfies the sampled sequence (T models clk and a),
  // _|_^omega does not, so U is disabled.
  EXPECT_TRUE(DisablesTopLevelClocked(Word{A({"d"})}, *u));
  // No letter satisfies d, so the disabling condition never fires.
  EXPECT_FALSE(DisablesTopLevelClocked(Word{A({"clk", "a"})}, *u));
  // A bare clocked property is never disabled.
  EXPECT_FALSE(DisablesTopLevelClocked(Word{A({"clk", "a"})},
                                       *ClockedTopProperty(ClockedStrongA())));
}

// §F.5.3.1: the pass/disabled/fail trichotomy carries over to U.
TEST(ClockedTopLevel, PassDisabledFailTrichotomy) {
  auto bare = ClockedTopProperty(ClockedStrongA());
  EXPECT_TRUE(PassesTopLevelClocked(Word{A({"clk", "a"})}, *bare));
  EXPECT_FALSE(FailsTopLevelClocked(Word{A({"clk", "a"})}, *bare));
  // No clk tick and no disable: the property neither passes nor is disabled.
  EXPECT_TRUE(FailsTopLevelClocked(Word{A({"x"})}, *bare));

  auto guarded = ClockedTopDisableIff(BoolAtom("d"), ClockedStrongA());
  EXPECT_TRUE(IsDisabledTopLevelClocked(Word{A({"d"})}, *guarded));
  EXPECT_FALSE(FailsTopLevelClocked(Word{A({"d"})}, *guarded));
}

// Builders for the assertion-statement tests: an unclocked top-level body
// strong(name), evaluated under an explicit @(clk).
auto BodyStrong(const std::string& name) {
  return TopProperty(PropStrong(BoolSeq(name)));
}

// §F.5.3.1: w, b |= always @(c) assert property T iff at every index where the
// clock and enabling condition hold, the body passes or is disabled.
TEST(Assertion, AlwaysClockedAssertChecksEveryClockTick) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kAlways,
                              AssertionStatement::Role::kAssert,
                              BoolAtom("clk"), BodyStrong("a"));
  // clk tick with a: the body passes.
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolTrue(), *a));
  // clk tick without a: the body fails at the activation point.
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolTrue(), *a));
  // No clk tick: no activation, so the assert holds vacuously.
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"x"})}, *BoolTrue(), *a));
}

// §F.5.3.1: w, b |= always @(c) assume property T iff w, b |= always @(c)
// assert property T -- assume shares the assert definition.
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

// §F.5.3.1: w, b |= always @(c) cover property T iff some index has the clock,
// the enabling condition, and a passing body.
TEST(Assertion, AlwaysClockedCoverNeedsOnePassingTick) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kAlways,
                              AssertionStatement::Role::kCover, BoolAtom("clk"),
                              BodyStrong("a"));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolTrue(), *a));
  // A clk tick without a does not cover.
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolTrue(), *a));
  // No clk tick: nothing covers.
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"x"})}, *BoolTrue(), *a));
}

// §F.5.3.1: w, b |= initial @(c) assert property T fires only at the first clk
// tick (the prefix tightly satisfies !c [*0:$] ##1 c).
TEST(Assertion, InitialClockedAssertFiresAtFirstClockTick) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kInitial,
                              AssertionStatement::Role::kAssert,
                              BoolAtom("clk"), BodyStrong("a"));
  // First clk tick at index 1 with a present: passes.
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"x"}), A({"clk", "a"})},
                                          *BoolTrue(), *a));
  // First clk tick at index 1 without a: fails.
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"x"}), A({"clk"})}, *BoolTrue(), *a));
  // No clk tick at all: the initial obligation never activates.
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"x"}), A({"y"})}, *BoolTrue(), *a));
}

// §F.5.3.1: the enabling condition gates activation -- when b fails at the
// activation index, the obligation does not fire.
TEST(Assertion, EnablingConditionGatesActivation) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kAlways,
                              AssertionStatement::Role::kAssert,
                              BoolAtom("clk"), BodyStrong("a"));
  // The body would fail at the clk tick, but b = en is absent, so no
  // activation and the assert holds.
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolAtom("en"), *a));
  // With en present alongside the failing tick, the obligation fires and fails.
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "en"})}, *BoolAtom("en"), *a));
}

// §F.5.3.1: w, b |= always assume property U / cover property U use the
// intrinsically clocked body U with no explicit leading clock.
TEST(Assertion, ClockedTopBodyUsesTheIntrinsicClock) {
  auto cover = AssertionWithClockedTop(AssertionStatement::Activation::kAlways,
                                       AssertionStatement::Role::kCover,
                                       ClockedTopProperty(ClockedStrongA()));
  // Some index where the clocked body passes: covered.
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolTrue(), *cover));
  // The clocked body never passes here: not covered.
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"x"})}, *BoolTrue(), *cover));
}

// §F.5.3.1: a word is feasible iff every assumption is satisfied on it; an
// assert statement is satisfied on the set iff it holds on each feasible word,
// and holds globally under the same condition.
TEST(WordSet, FeasibilityAndAssertSatisfaction) {
  EnabledAssertion assumption{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssume, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  std::vector<EnabledAssertion> assumptions{assumption};

  const Word kFeasible = {A({"clk", "a"})};
  const Word kInfeasible = {A({"clk"})};  // the assume (strong a at clk) fails
  EXPECT_TRUE(WordIsFeasible(kFeasible, assumptions));
  EXPECT_FALSE(WordIsFeasible(kInfeasible, assumptions));

  std::vector<Word> words{kFeasible, kInfeasible};

  EnabledAssertion holds{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssert, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  // Only the feasible word is checked, and the assert holds on it.
  EXPECT_TRUE(AssertSatisfiedOnWordSet(holds, words, assumptions));
  EXPECT_TRUE(HoldsGloballyOnWordSet(holds, words, assumptions));

  EnabledAssertion fails{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssert, BoolAtom("clk"),
                          BodyStrong("b")),
      BoolTrue()};
  // The feasible word has no b at the clk tick, so the assert is not satisfied
  // on the set.
  EXPECT_FALSE(AssertSatisfiedOnWordSet(fails, words, assumptions));
}

// §F.5.3.1: a cover statement is satisfied on the set iff it holds on at least
// one feasible word.
TEST(WordSet, CoverSatisfactionNeedsOneFeasibleWitness) {
  std::vector<EnabledAssertion> no_assumptions;
  std::vector<Word> words{Word{A({"x"})}, Word{A({"clk", "a"})}};

  EnabledAssertion cover{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kCover, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  // The second word covers, so the cover is satisfied on the set.
  EXPECT_TRUE(CoverSatisfiedOnWordSet(cover, words, no_assumptions));

  EnabledAssertion uncovered{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kCover, BoolAtom("clk"),
                          BodyStrong("z")),
      BoolTrue()};
  // No word has z at a clk tick, so nothing covers.
  EXPECT_FALSE(CoverSatisfiedOnWordSet(uncovered, words, no_assumptions));
}

// §F.5.3.1: w, b |= always assert property U checks, at every enabled index,
// that the intrinsically clocked body passes or is disabled -- there is no
// explicit leading clock to gate activation.
TEST(Assertion, AlwaysAssertUUsesTheIntrinsicClock) {
  auto a = AssertionWithClockedTop(AssertionStatement::Activation::kAlways,
                                   AssertionStatement::Role::kAssert,
                                   ClockedTopProperty(ClockedStrongA()));
  // The clocked body passes at index 0: the assert holds.
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolTrue(), *a));
  // A clk tick without a: the body fails at the activation point.
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolTrue(), *a));
}

// §F.5.3.1: w, b |= initial assert property U fires only at index 0, so a later
// index that would fail under the always form is ignored.
TEST(Assertion, InitialAssertUFiresOnlyAtIndexZero) {
  auto a = AssertionWithClockedTop(AssertionStatement::Activation::kInitial,
                                   AssertionStatement::Role::kAssert,
                                   ClockedTopProperty(ClockedStrongA()));
  // Index 0 satisfies the body, and the trailing letter is never examined.
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"clk", "a"}), A({"x"})},
                                          *BoolTrue(), *a));
  // Index 0 fails the body.
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolTrue(), *a));
}

// §F.5.3.1: w, b |= always assume property U iff w, b |= always assert property
// U -- assume shares the assert definition for the U body too.
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

// §F.5.3.1: w, b |= initial @(c) assume property T iff w, b |= initial @(c)
// assert property T.
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

// §F.5.3.1: w, b |= initial assume property U iff w, b |= initial assert
// property U.
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

// §F.5.3.1: w, b |= initial @(c) cover property T fires at the first clk tick
// and is covered when the body passes there.
TEST(Assertion, InitialClockedCoverFiresAtFirstTick) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kInitial,
                              AssertionStatement::Role::kCover, BoolAtom("clk"),
                              BodyStrong("a"));
  // First clk tick at index 1 with a present: covered.
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"x"}), A({"clk", "a"})},
                                          *BoolTrue(), *a));
  // First clk tick at index 1 without a: not covered.
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"x"}), A({"clk"})}, *BoolTrue(), *a));
  // No clk tick: the initial cover never activates, so nothing covers.
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"x"}), A({"y"})}, *BoolTrue(), *a));
}

// §F.5.3.1: w, b |= initial cover property U is covered iff the enabling
// condition holds at index 0 and the clocked body passes on the whole word.
TEST(Assertion, InitialCoverUFiresAtIndexZero) {
  auto a = AssertionWithClockedTop(AssertionStatement::Activation::kInitial,
                                   AssertionStatement::Role::kCover,
                                   ClockedTopProperty(ClockedStrongA()));
  EXPECT_TRUE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolTrue(), *a));
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"})}, *BoolTrue(), *a));
  // The enabling condition fails at index 0, so the cover never activates.
  EXPECT_FALSE(
      NeutrallySatisfiesAssertion(Word{A({"clk", "a"})}, *BoolAtom("en"), *a));
}

// §F.5.3.1: w |=^d ( U ) iff w |=^d U -- disabling propagates through a
// parenthesized clocked top-level property.
TEST(ClockedTopLevel, ParenthesizedDisablingPropagates) {
  auto u =
      ClockedTopParen(ClockedTopDisableIff(BoolAtom("d"), ClockedStrongA()));
  // d at index 0 makes the T^omega and _|_^omega completions diverge, so the
  // parenthesized U is disabled.
  EXPECT_TRUE(DisablesTopLevelClocked(Word{A({"d"})}, *u));
  // No letter satisfies d, so disabling does not fire.
  EXPECT_FALSE(DisablesTopLevelClocked(Word{A({"clk", "a"})}, *u));
}

// §F.5.3.1 edge: w, b |= always @(c) assert property T quantifies over every
// clock tick, so a word that passes at the first tick but fails at a later one
// is not satisfied.
TEST(Assertion, AlwaysClockedAssertFailsWhenALaterTickFails) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kAlways,
                              AssertionStatement::Role::kAssert,
                              BoolAtom("clk"), BodyStrong("a"));
  // Index 0 passes (a at the tick), index 1 fails (no a at the tick).
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk", "a"}), A({"clk"})},
                                           *BoolTrue(), *a));
  // Every tick passes: the assert holds.
  EXPECT_TRUE(NeutrallySatisfiesAssertion(
      Word{A({"clk", "a"}), A({"clk", "a"})}, *BoolTrue(), *a));
}

// §F.5.3.1 edge: w, b |= always @(c) cover property T is existential over
// indices, so a witness at a later tick suffices even when earlier ticks fail.
TEST(Assertion, AlwaysClockedCoverFiresAtALaterTick) {
  auto a = AssertionWithClock(AssertionStatement::Activation::kAlways,
                              AssertionStatement::Role::kCover, BoolAtom("clk"),
                              BodyStrong("a"));
  // Index 0 (clk, no a) does not cover, but index 1 (clk and a) does.
  EXPECT_TRUE(NeutrallySatisfiesAssertion(Word{A({"clk"}), A({"clk", "a"})},
                                          *BoolTrue(), *a));
  // No tick carries a, so nothing covers.
  EXPECT_FALSE(NeutrallySatisfiesAssertion(Word{A({"clk"}), A({"clk"})},
                                           *BoolTrue(), *a));
}

// §F.5.3.1 edge: for T = disable iff (b) P, the cutoff prefix is fixed by the
// LEAST index whose letter satisfies b. Here b first fires at index 1, so the
// _|_^omega completion of the single-letter prefix decides P; a later firing
// index would have admitted the longer prefix that satisfies P.
TEST(NeutralSatisfaction, DisableIffUsesLeastSatisfyingIndex) {
  auto t = TopDisableIff(BoolAtom("d"),
                         PropStrong(SeqConcat(BoolSeq("a"), BoolSeq("b"))));
  // d holds at index 1 and index 2. The least index is 1, so the prefix is
  // [a]: under _|_^omega, (a ##1 b) cannot complete, so T is not satisfied.
  EXPECT_FALSE(
      NeutrallySatisfiesTopLevel(Word{A({"a"}), A({"b", "d"}), A({"d"})}, *t));
  // The same word with d removed from index 1 pushes the least index to 2; the
  // prefix [a][b] now completes (a ##1 b) under either completion, so T holds.
  EXPECT_TRUE(
      NeutrallySatisfiesTopLevel(Word{A({"a"}), A({"b"}), A({"d"})}, *t));
}

// §F.5.3.1 edge: w |= ( P1 until P2 ) holds when P2 releases on the very first
// suffix, leaving no obligation on P1.
TEST(NeutralSatisfaction, UntilReleasesImmediately) {
  auto p = PropUntil(PropStrong(BoolSeq("a")), PropStrong(BoolSeq("b")));
  // The whole word satisfies P2 at suffix 0, so no earlier suffix must satisfy
  // P1 -- even though [b] does not satisfy strong(a).
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"b"})}, *p));
}

// §F.5.3.1 edge: an assert statement is satisfied on a set vacuously when no
// word is feasible, while a cover statement on the same empty feasible subset
// is not satisfied (it has no feasible witness).
TEST(WordSet, VacuousWhenEveryWordIsInfeasible) {
  EnabledAssertion assumption{
      *AssertionWithClock(AssertionStatement::Activation::kAlways,
                          AssertionStatement::Role::kAssume, BoolAtom("clk"),
                          BodyStrong("a")),
      BoolTrue()};
  std::vector<EnabledAssertion> assumptions{assumption};
  // The lone word fails the assumption (no a at the clk tick), so it is
  // infeasible and the feasible subset is empty.
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

// §F.5.3.1 edge: a word is feasible only when EVERY assumption is satisfied on
// it; one failing assumption makes the word infeasible.
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
  // a holds at the tick but b does not: the second assumption fails.
  EXPECT_FALSE(WordIsFeasible(Word{A({"clk", "a"})}, assumptions));
  // Both a and b hold at the tick: every assumption is satisfied.
  EXPECT_TRUE(WordIsFeasible(Word{A({"clk", "a", "b"})}, assumptions));
}

}  // namespace
