#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

using namespace delta;

namespace {

// A single alphabet letter carrying the given atomic propositions.
Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// A Boolean leaf sequence b.
auto Bool(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// A local-variable sampling sequence (1, v = e).
auto Samp(const std::string& name) { return SeqLocalVarSampling(name); }

// §F.5.6.1 (strong): w, L_0 |= strong(R) iff some prefix tightly satisfies R
// under the four-way relation. The sequence operand may itself carry local
// variables, so a sampling and a local-variable declaration are valid R.
TEST(NeutralSatisfactionLocals, StrongUsesFourWayRelation) {
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"})}, *LvStrong(Bool("a")),
                                           LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(
      Word{A({"b"})}, *LvStrong(Bool("a")), LocalContext{}));
  // A sampling sequence matches any single letter, so strong holds on a
  // one-letter word and fails on the empty word (no nonempty prefix).
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"x"})}, *LvStrong(Samp("v")),
                                           LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{}, *LvStrong(Samp("v")),
                                            LocalContext{}));
  // The verdict does not depend on the input context's values; an unrelated
  // incoming binding does not change it.
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"x"})}, *LvStrong(Samp("v")),
                                           LocalContext{{"u", A({"z"})}}));
  // The underlying sequence may declare a local variable.
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      Word{A({"x"})}, *LvStrong(SeqLocalVarDecl("int", "v", Samp("v"))),
      LocalContext{}));
}

// §F.5.6.1 (weak): w, L_0 |= weak(R) iff every T^omega-completed prefix
// satisfies strong(R). On the empty word the universal is vacuous, so weak
// holds where strong does not -- the defining contrast between the two.
TEST(NeutralSatisfactionLocals, WeakIsVacuousOnEmptyWordAndCompletesPrefixes) {
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{}, *LvWeak(Bool("a")), LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{}, *LvStrong(Bool("a")),
                                            LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"})}, *LvWeak(Bool("a")),
                                           LocalContext{}));
  // A prefix that can never satisfy strong(b) under a T^omega tail fails weak.
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"b"})}, *LvWeak(Bool("a")),
                                            LocalContext{}));
}

// §F.5.6.1 (not), printed p.1249: w, L_0 |= not P iff w-bar, L_0 |= P --
// negation is by word complementation, NOT a logical negation of the verdict
// (only the boolean Remark, w |= not b iff w |= !b, negates). This mirrors the
// plain neutral-satisfaction rule §F.5.3.1, so the local-variable layer agrees
// with it letter for letter (cf. NeutralSatisfaction.NotEvaluatesAgainstThe-
// ComplementWord / NotLeavesAtomLettersUnchanged in test_..._annex_f_05_03_01).
TEST(NeutralSatisfactionLocals, NotEvaluatesAgainstTheComplementWord) {
  // Over atom-set letters the complement is the identity, so not strong(a)
  // tracks strong(a): false where a is absent, true where a holds.
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(
      Word{A({"b"})}, *LvNot(LvStrong(Bool("a"))), LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      Word{A({"a"})}, *LvNot(LvStrong(Bool("a"))), LocalContext{}));
  // The rule is evaluated on w-bar, so the T/_|_ swap is observable: over [T]
  // the property is checked on the complement [_|_], where _|_ |= a fails, so
  // strong(a) fails on w-bar and (no logical negation) not strong(a) fails too.
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(
      Word{LetterTop()}, *LvNot(LvStrong(Bool("a"))), LocalContext{}));
  // Dually, over [_|_] the property is checked on [T], where strong(a) holds,
  // so not strong(a) holds.
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      Word{LetterBottom()}, *LvNot(LvStrong(Bool("a"))), LocalContext{}));
}

// §F.5.6.1 (or, and): the Boolean combinators distribute neutral satisfaction
// over their operands under the same context.
TEST(NeutralSatisfactionLocals, OrAndCombineOperands) {
  auto disj = LvOr(LvStrong(Bool("a")), LvStrong(Bool("b")));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *disj, LocalContext{}));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"c"})}, *disj, LocalContext{}));
  auto conj = LvAnd(LvStrong(Bool("a")), LvStrong(Bool("b")));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *conj, LocalContext{}));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"a", "b"})}, *conj, LocalContext{}));
}

// §F.5.6.1 (nexttime): w, L_0 |= ( nexttime P ) iff |w| = 0 or w^{1.}, L_0 |=
// P.
TEST(NeutralSatisfactionLocals, NexttimeAdvancesOneLetter) {
  auto prop = LvNexttime(LvStrong(Bool("b")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"b"})}, *prop,
                                           LocalContext{}));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *prop, LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{}, *prop, LocalContext{}));
}

// §F.5.6.1 (until): w, L_0 |= ( P1 until P2 ) holds when P2 eventually holds at
// a suffix with P1 holding on every earlier suffix, or P1 holds throughout.
TEST(NeutralSatisfactionLocals, UntilHoldsUntilSecondOperand) {
  auto prop = LvUntil(LvStrong(Bool("a")), LvStrong(Bool("b")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"b"})}, *prop,
                                           LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"c"})}, *prop,
                                            LocalContext{}));
}

// §F.5.6.1 (accept_on): w, L_0 |= ( accept_on (b) P ) iff w, L_0 |= P, or some
// letter satisfies b and the T^omega-completed prefix before it satisfies P.
TEST(NeutralSatisfactionLocals, AcceptOnPassesOnAbortPrefix) {
  auto prop = LvAcceptOn(BoolAtom("b"), LvStrong(Bool("a")));
  // P already holds, so accept_on holds without consulting the abort.
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *prop, LocalContext{}));
  // P fails, but the abort fires at index 0 and the T^omega completion of the
  // empty prefix satisfies strong(a).
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"b"})}, *prop, LocalContext{}));
  // Neither P nor the abort holds.
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"c"})}, *prop, LocalContext{}));
}

// §F.5.6.1 (paren): w, L_0 |= ( P ) iff w, L_0 |= P.
TEST(NeutralSatisfactionLocals, ParenIsTransparent) {
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      Word{A({"a"})}, *LvParen(LvStrong(Bool("a"))), LocalContext{}));
}

// §F.5.6.1 (implication): w, L_0 |= ( R |-> P ) iff for every match of R on a
// prefix of w-bar, the consequent holds on the matching suffix under each
// output context the antecedent yields. The antecedent may bind a local
// variable, whose binding is threaded into the consequent.
TEST(NeutralSatisfactionLocals, ImplicationThreadsAntecedentOutputs) {
  // Antecedent samples v at index 0 and the consequent holds on the suffix.
  auto holds = LvImplication(Samp("v"), LvStrong(Samp("w")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"b"})}, *holds,
                                           LocalContext{}));
  // The antecedent matches but the consequent fails on the matching suffix.
  auto fails = LvImplication(Samp("v"), LvStrong(Bool("z")));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *fails, LocalContext{}));
  // The antecedent never matches, so the implication is vacuously satisfied.
  auto vacuous = LvImplication(Bool("q"), LvStrong(Bool("z")));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *vacuous, LocalContext{}));
}

// §F.5.6.1 (local variable declaration): w, L_0 |= ( t v ; P ) iff
// w, L_0\v |= P. The declared name is stripped from the context the body sees;
// the body's verdict is then the property's verdict.
TEST(NeutralSatisfactionLocals, PropertyDeclarationScopesTheName) {
  auto decl = LvLocalVarDecl("int", "v", LvStrong(Samp("v")));
  // Empty context: removing v is a no-op and the body holds.
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"x"})}, *decl, LocalContext{}));
  // An incoming v is hidden from the body; the body still holds on its own.
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"x"})}, *decl,
                                           LocalContext{{"v", A({"old"})}}));
  // The body's verdict passes through the declaration when the body fails.
  auto decl_fail = LvLocalVarDecl("int", "v", LvStrong(Bool("a")));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"b"})}, *decl_fail, LocalContext{}));
  // Declarations nest.
  auto nested = LvLocalVarDecl("int", "v",
                               LvLocalVarDecl("int", "w", LvStrong(Samp("w"))));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"x"})}, *nested, LocalContext{}));
}

// §F.5.6.1 (entry): "w |= Q iff w, {} |= Q." The context-free overload starts
// the recursion from the empty context and agrees with passing {} explicitly.
TEST(NeutralSatisfactionLocals, EmptyContextEntryPoint) {
  auto prop = LvStrong(Bool("a"));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"})}, *prop));
  EXPECT_EQ(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *prop),
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *prop, LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"b"})}, *prop));
}

// §F.5.6.1 (top-level T = P): w, L_0 |= T iff w, L_0 |= P, and a bare property
// is never disabled, so the pass/fail verdict follows the property directly.
TEST(NeutralSatisfactionLocals, TopLevelBarePropertyPassesAndFails) {
  auto top = LvTopProperty(LvStrong(Bool("a")));
  EXPECT_TRUE(PassesTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  EXPECT_FALSE(
      IsDisabledTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  EXPECT_FALSE(FailsTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  // The property fails and a bare property is never disabled, so T fails.
  EXPECT_FALSE(PassesTopLevelWithLocals(Word{A({"b"})}, *top, LocalContext{}));
  EXPECT_FALSE(
      IsDisabledTopLevelWithLocals(Word{A({"b"})}, *top, LocalContext{}));
  EXPECT_TRUE(FailsTopLevelWithLocals(Word{A({"b"})}, *top, LocalContext{}));
}

// §F.5.6.1 (top-level disable iff): when no letter satisfies the guard, T
// passes iff the guarded property holds; when the guard first fires, the prefix
// before it is completed with _|_^omega for the pass test, and the disabling
// test compares the T^omega and _|_^omega completions.
TEST(NeutralSatisfactionLocals, TopLevelDisableIffPassesAndDisables) {
  auto top = LvTopDisableIff(BoolAtom("g"), LvStrong(Bool("a")));
  // No guard letter: T passes exactly when the property holds.
  EXPECT_TRUE(PassesTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  EXPECT_FALSE(
      IsDisabledTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  // The guard fires at index 0: the empty prefix completed with _|_^omega does
  // not satisfy strong(a), so T does not pass; but the T^omega completion does
  // while the _|_^omega completion does not, so T is disabled.
  EXPECT_FALSE(PassesTopLevelWithLocals(Word{A({"g"})}, *top, LocalContext{}));
  EXPECT_TRUE(
      IsDisabledTopLevelWithLocals(Word{A({"g"})}, *top, LocalContext{}));
  // Pass and disabled are mutually exclusive, so a disabled T does not fail.
  EXPECT_FALSE(FailsTopLevelWithLocals(Word{A({"g"})}, *top, LocalContext{}));
  EXPECT_FALSE(
      PassesTopLevelWithLocals(Word{A({"g"})}, *top, LocalContext{}) &&
      IsDisabledTopLevelWithLocals(Word{A({"g"})}, *top, LocalContext{}));
}

// §F.5.6.1 (top-level paren): w, L_0 |= ( T ) iff w, L_0 |= T, for both the
// pass and the disabling relations.
TEST(NeutralSatisfactionLocals, TopLevelParenIsTransparent) {
  auto top = LvTopParen(LvTopProperty(LvStrong(Bool("a"))));
  EXPECT_TRUE(PassesTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  auto guarded =
      LvTopParen(LvTopDisableIff(BoolAtom("g"), LvStrong(Bool("a"))));
  EXPECT_TRUE(
      IsDisabledTopLevelWithLocals(Word{A({"g"})}, *guarded, LocalContext{}));
}

// §F.5.6.1 (top-level declaration): w, L_0 |= ( t v ; T ) iff w, L_0\v |= T,
// and likewise w, L_0 |=^d ( t v ; T ) iff w, L_0\v |=^d T. The declaration is
// transparent to the pass and disabling verdicts, with the declared name hidden
// from the body.
TEST(NeutralSatisfactionLocals, TopLevelDeclarationScopesTheName) {
  auto top = LvTopLocalVarDecl("int", "v", LvTopProperty(LvStrong(Samp("v"))));
  EXPECT_TRUE(PassesTopLevelWithLocals(Word{A({"x"})}, *top, LocalContext{}));
  EXPECT_TRUE(PassesTopLevelWithLocals(Word{A({"x"})}, *top,
                                       LocalContext{{"v", A({"old"})}}));
  auto top_fail =
      LvTopLocalVarDecl("int", "v", LvTopProperty(LvStrong(Bool("a"))));
  EXPECT_TRUE(
      FailsTopLevelWithLocals(Word{A({"b"})}, *top_fail, LocalContext{}));
  // Disabling threads through the declaration.
  auto top_disable = LvTopLocalVarDecl(
      "int", "v", LvTopDisableIff(BoolAtom("g"), LvStrong(Bool("a"))));
  EXPECT_TRUE(IsDisabledTopLevelWithLocals(Word{A({"g"})}, *top_disable,
                                           LocalContext{}));
}

// --- Error conditions and boundary cases ---

// §F.5.6.1 (until) second disjunct: when P2 never holds at any suffix but P1
// holds at every suffix, the "P1 throughout" alternative makes until hold.
TEST(NeutralSatisfactionLocals, UntilHoldsWhenFirstOperandPersists) {
  auto prop = LvUntil(LvStrong(Bool("a")), LvStrong(Bool("z")));
  // strong(z) holds nowhere on [a, a]; strong(a) holds on every suffix.
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"a"})}, *prop,
                                           LocalContext{}));
}

// §F.5.6.1 (until) boundary: over the empty word both quantifiers range over an
// empty index set, so the "P1 throughout" alternative is vacuously satisfied.
TEST(NeutralSatisfactionLocals, UntilIsVacuousOverEmptyWord) {
  auto prop = LvUntil(LvStrong(Bool("a")), LvStrong(Bool("z")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{}, *prop, LocalContext{}));
}

// §F.5.6.1 (accept_on) error condition: P fails on the whole word and, although
// the abort fires at a later index, the T^omega-completed prefix before it does
// not satisfy P, so accept_on does not hold.
TEST(NeutralSatisfactionLocals, AcceptOnFailsWhenAbortPrefixDoesNotSatisfy) {
  auto prop = LvAcceptOn(BoolAtom("b"), LvStrong(Bool("a")));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"c"}), A({"b"})}, *prop,
                                            LocalContext{}));
}

// §F.5.6.1 (top-level disable iff) trichotomy fail: the guard fires, but the
// guarded property holds under neither the _|_^omega completion (so T does not
// pass) nor the T^omega completion (so T is not disabled); hence T fails.
TEST(NeutralSatisfactionLocals,
     TopLevelDisableIffFailsWhenNeitherPassNorDisabled) {
  auto top = LvTopDisableIff(BoolAtom("g"), LvStrong(Bool("z")));
  const Word kWord{A({"c"}), A({"g"})};
  EXPECT_FALSE(PassesTopLevelWithLocals(kWord, *top, LocalContext{}));
  EXPECT_FALSE(IsDisabledTopLevelWithLocals(kWord, *top, LocalContext{}));
  EXPECT_TRUE(FailsTopLevelWithLocals(kWord, *top, LocalContext{}));
}

// §F.5.6.1 (implication) boundary: over the empty word the antecedent matches
// no prefix, so the universal over matches is vacuously satisfied.
TEST(NeutralSatisfactionLocals, ImplicationIsVacuousOverEmptyWord) {
  auto prop = LvImplication(Samp("v"), LvStrong(Samp("w")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{}, *prop, LocalContext{}));
}

// §F.5.6.1 (implication) error condition: the consequent must hold at every
// matching prefix. The antecedent (an unbounded repeat of a) matches both the
// length-one and length-two prefixes; the consequent holds on the longer suffix
// but fails on the shorter one, so the implication fails.
TEST(NeutralSatisfactionLocals,
     ImplicationFailsWhenConsequentFailsAtLaterMatch) {
  auto prop = LvImplication(SeqUnboundedRepeat(Bool("a")),
                            LvNexttime(LvStrong(Bool("a"))));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"a"})}, *prop,
                                            LocalContext{}));
}

// §F.5.6.1 (or) right disjunct: w, L_0 |= ( P1 or P2 ) holds when only the
// second operand holds. The other or test observes the left disjunct (which
// short-circuits) and the both-false case; this one exercises the right half of
// the rule, where P1 fails and P2 alone carries the verdict.
TEST(NeutralSatisfactionLocals, OrSatisfiedByRightOperandAlone) {
  auto disj = LvOr(LvStrong(Bool("a")), LvStrong(Bool("b")));
  // strong(a) fails on [b], strong(b) holds, so the disjunction holds.
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"b"})}, *disj, LocalContext{}));
}

// §F.5.6.1 (top-level disable iff) no-guard edge: when no letter satisfies the
// guard, T's verdict is exactly the guarded property's verdict. The other
// disable iff tests cover the no-guard case with the property holding and the
// guard-fires cases; here no letter satisfies the guard and the property fails,
// so T does not pass, is not disabled, and therefore fails -- the failing leg
// of the trichotomy reached through the no-guard branch.
TEST(NeutralSatisfactionLocals,
     TopLevelDisableIffFailsWhenUnguardedPropertyFails) {
  auto top = LvTopDisableIff(BoolAtom("g"), LvStrong(Bool("a")));
  const Word kWord{
      A({"c"})};  // no 'g' guard letter, and strong(a) fails on [c]
  EXPECT_FALSE(PassesTopLevelWithLocals(kWord, *top, LocalContext{}));
  EXPECT_FALSE(IsDisabledTopLevelWithLocals(kWord, *top, LocalContext{}));
  EXPECT_TRUE(FailsTopLevelWithLocals(kWord, *top, LocalContext{}));
}

}  // namespace
