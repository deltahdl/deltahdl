#include <gtest/gtest.h>

#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "elaborator/annex_f_vacuity_local_variables.h"

using namespace delta;

namespace {

Letter L(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// A single-letter Boolean sequence matching the named atom.
auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// A local-variable sampling sequence (1, v = e).
auto Samp(const std::string& name) { return SeqLocalVarSampling(name); }

// strong( name ): nonvacuous on every word (a §F.5.3.3 base case, inherited by
// §F.5.6.3 over the local-variable property model).
auto Strong(const std::string& name) { return LvStrong(Bs(name)); }

// ( name |-> strong( t ) ): a property whose non-vacuity depends on the word --
// nonvacuous exactly when the single-letter trigger `name` matches a prefix.
// Used to exercise the inductive rules that recurse into a word-sensitive
// operand.
auto Trig(const std::string& name) {
  return LvImplication(Bs(name), Strong("t"));
}

// --- §F.5.6.3 C1: the §F.5.3.3 rules realized over the local-variable model,
// threading an input context. With local-variable-free properties and the empty
// context the four-way relation collapses to tight satisfaction, so the
// verdicts match §F.5.3.3 exactly. ---

// §F.5.3.3 base: w, L_0 |=^non strong(R) and weak(R) hold for every w; the
// context plays no role.
TEST(NonVacuityLocals, StrongAndWeakAreAlwaysNonvacuous) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *Strong("a"),
                                              LocalContext{}));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesWithLocals(Word{}, *Strong("a"), LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *LvWeak(Bs("a")),
                                              LocalContext{}));
  // An unrelated incoming binding does not change the verdict.
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{}, *Strong("a"),
                                              LocalContext{{"u", L({"z"})}}));
}

// §F.5.3.3: w, L_0 |=^non ( P ) iff w, L_0 |=^non P -- a parenthesis is
// transparent.
TEST(NonVacuityLocals, ParenthesisIsTransparent) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"a"})}, *LvParen(Trig("a")), LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"})}, *LvParen(Trig("a")), LocalContext{}));
}

// §F.5.3.3: w, L_0 |=^non R |-> P iff some prefix w^{0,i} tightly satisfies the
// trigger R -- on w itself -- and the matching suffix is nonvacuous for P. A
// trigger that never matches leaves the implication vacuous.
TEST(NonVacuityLocals, ImplicationNeedsTheTriggerToMatch) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *Trig("a"),
                                              LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *Trig("a"),
                                               LocalContext{}));
}

// §F.5.6.3: the implication threads each output context the antecedent yields
// into the consequent's non-vacuity. A sampling antecedent (1, v = e) matches a
// one-letter prefix and binds v; the consequent is then nonvacuous on the
// matching suffix, so the four-way relation is observably used.
TEST(NonVacuityLocals, ImplicationThreadsAntecedentOutputContexts) {
  auto prop = LvImplication(Samp("v"), LvStrong(Samp("w")));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"}), L({"b"})}, *prop,
                                              LocalContext{}));
  // The empty word has no prefix for the antecedent to match, so it is vacuous.
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{}, *prop, LocalContext{}));
}

// §F.5.3.3: w, L_0 |=^non ( P1 or P2 ) iff either side is nonvacuous.
TEST(NonVacuityLocals, DisjunctionIsNonvacuousWhenEitherSideIs) {
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"})}, *LvOr(Trig("a"), Trig("a")), LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"})}, *LvOr(Trig("a"), Strong("s")), LocalContext{}));
}

// §F.5.3.3: w, L_0 |=^non ( P1 and P2 ) iff *either* conjunct is nonvacuous,
// even when the other is vacuous on w.
TEST(NonVacuityLocals, ConjunctionIsNonvacuousWhenEitherSideIs) {
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"})}, *LvAnd(Trig("a"), Trig("a")), LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"})}, *LvAnd(Strong("s"), Trig("a")), LocalContext{}));
}

// §F.5.3.3: w, L_0 |=^non not P iff w-bar, L_0 |=^non P. The complement turns a
// lone _|_ (which leaves Trig("a") vacuous) into a T that matches the trigger.
TEST(NonVacuityLocals, NegationEvaluatesOnTheComplement) {
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{LetterBottom()}, *Trig("a"),
                                               LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{LetterBottom()}, *LvNot(Trig("a")), LocalContext{}));
}

// §F.5.3.3: w, L_0 |=^non nexttime P iff |w| > 0 and w^{1.}, L_0 |=^non P.
TEST(NonVacuityLocals, NexttimeRequiresANonemptyWord) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"a"})}, *LvNexttime(Strong("b")), LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{}, *LvNexttime(Strong("b")),
                                               LocalContext{}));
}

// §F.5.3.3: w, L_0 |=^non ( P1 until P2 ) needs an index where one operand
// becomes nonvacuous, with the guard "P1 and not P2" holding neutrally before
// it. The witness may lie past index 0.
TEST(NonVacuityLocals, UntilNeedsAnOperandToBecomeNonvacuous) {
  auto until = LvUntil(Trig("a"), Trig("a"));
  EXPECT_FALSE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *until, LocalContext{}));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *until, LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"x"}), L({"a"})}, *until,
                                              LocalContext{}));
}

// §F.5.3.3: w, L_0 |=^non accept_on (b) P requires the operand to be nonvacuous
// together with the abort condition. When no letter satisfies b the no-abort
// alternative holds; with the only letter satisfying b non-vacuity can come
// only through the prefix alternative; and a vacuous operand makes the whole
// vacuous.
TEST(NonVacuityLocals, AcceptOnFollowsTheAbortShape) {
  auto good = LvAcceptOn(BoolAtom("b"), Strong("s"));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"s"})}, *good, LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"b", "s"})}, *good,
                                              LocalContext{}));
  auto vacuous = LvAcceptOn(BoolAtom("b"), Trig("a"));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *vacuous,
                                               LocalContext{}));
}

// §F.5.3.3 at the top level: a bare property defers to the property rule; the
// disable iff guard shares accept_on's abort shape; a parenthesis is
// transparent.
TEST(NonVacuityLocals, TopLevelDisableIffUsesTheAbortShape) {
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevelWithLocals(
      Word{L({"s"})}, *LvTopDisableIff(BoolAtom("b"), Strong("s")),
      LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesTopLevelWithLocals(
      Word{L({"x"})}, *LvTopDisableIff(BoolAtom("b"), Trig("a")),
      LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevelWithLocals(
      Word{L({"a"})}, *LvTopProperty(Trig("a")), LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevelWithLocals(
      Word{L({"a"})}, *LvTopParen(LvTopProperty(Trig("a"))), LocalContext{}));
}

// §F.5.6.3 inherits §F.5.3.3's "w satisfies P nonvacuously iff w |= P and
// w |=^non P," realized with locals. A genuine match satisfies both relations;
// a vacuous pass (a trigger that never fires) is neutrally satisfied yet
// rejected.
TEST(NonVacuityLocals, NonvacuousSatisfactionCombinesBothRelations) {
  EXPECT_TRUE(SatisfiesNonVacuouslyWithLocals(Word{L({"s"})}, *Strong("s"),
                                              LocalContext{}));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{L({"x"})}, *Trig("a"), LocalContext{}));
  EXPECT_FALSE(SatisfiesNonVacuouslyWithLocals(Word{L({"x"})}, *Trig("a"),
                                               LocalContext{}));
  EXPECT_TRUE(SatisfiesTopLevelNonVacuouslyWithLocals(
      Word{L({"s"})}, *LvTopProperty(Strong("s")), LocalContext{}));
  EXPECT_FALSE(SatisfiesTopLevelNonVacuouslyWithLocals(
      Word{L({"x"})}, *LvTopProperty(Trig("a")), LocalContext{}));
}

// §F.5.6.3: the empty-context entry overload starts the recursion from no live
// local variables and agrees with passing {} explicitly.
TEST(NonVacuityLocals, EmptyContextEntryPoint) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *Strong("a")));
  EXPECT_EQ(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *Trig("a")),
            NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *Trig("a"),
                                            LocalContext{}));
}

// --- §F.5.6.3 C2: the local-variable declaration rule, the one rule this
// subclause states explicitly. ---

// §F.5.6.3: w, L_0 |=^non ( t v ; P ) iff w, L_0\v |=^non P. The declaration's
// verdict equals the body's verdict under the context with v removed, the
// body's verdict passes through (both true and false), an incoming binding for
// v is hidden, and declarations nest.
TEST(NonVacuityLocals, PropertyDeclarationStripsTheNameFromTheContext) {
  auto body = Trig("a");
  auto decl = LvLocalVarDecl("int", "v", body);
  const LocalContext kCtx{{"v", L({"old"})}, {"u", L({"z"})}};

  // The declaration's verdict is exactly the body's verdict under L_0\v, for a
  // word where the body is nonvacuous and one where it is not.
  EXPECT_EQ(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *decl, kCtx),
            NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *body,
                                            RemoveName(kCtx, "v")));
  EXPECT_EQ(NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *decl, kCtx),
            NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *body,
                                            RemoveName(kCtx, "v")));

  // The verdict passes through: nonvacuous body -> nonvacuous declaration;
  // vacuous body -> vacuous declaration. The incoming v does not change either.
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *decl, kCtx));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *decl, kCtx));

  // Removing v from the empty context is a no-op; the body's verdict stands.
  EXPECT_TRUE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *decl, LocalContext{}));

  // Declarations nest, each stripping its own name.
  auto nested =
      LvLocalVarDecl("int", "v", LvLocalVarDecl("int", "w", Trig("a")));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *nested, LocalContext{}));
  EXPECT_FALSE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *nested, LocalContext{}));
}

// §F.5.6.3 at the top level: w, L_0 |=^non ( t v ; T ) iff w, L_0\v |=^non T.
// The declaration is transparent to the verdict with the declared name hidden
// from the body.
TEST(NonVacuityLocals, TopLevelDeclarationStripsTheNameFromTheContext) {
  auto body = LvTopProperty(Trig("a"));
  auto top = LvTopLocalVarDecl("int", "v", body);
  const LocalContext kCtx{{"v", L({"old"})}};

  EXPECT_EQ(NonVacuouslyEvaluatesTopLevelWithLocals(Word{L({"a"})}, *top, kCtx),
            NonVacuouslyEvaluatesTopLevelWithLocals(Word{L({"a"})}, *body,
                                                    RemoveName(kCtx, "v")));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesTopLevelWithLocals(Word{L({"a"})}, *top, kCtx));
  EXPECT_FALSE(
      NonVacuouslyEvaluatesTopLevelWithLocals(Word{L({"x"})}, *top, kCtx));
}

// --- §F.5.6.3 C1: error conditions and edge cases of the §F.5.3.3 rules,
// realized over the local-variable model. ---

// §F.5.3.3 edge case: ( P1 until P2 ) needs an index 0 <= i < |w| witnessing
// one operand's non-vacuity, so over the empty word there is no such index and
// the until is vacuous.
TEST(NonVacuityLocals, UntilIsVacuousOverTheEmptyWord) {
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{}, *LvUntil(Trig("a"), Trig("a")), LocalContext{}));
}

// §F.5.3.3 edge case: nexttime is not merely a length gate -- past the |w| > 0
// check it defers to non-vacuity of the suffix. On a one-letter word the suffix
// is empty after the shift, leaving the trigger property vacuous, so nexttime
// is vacuous even though the word is nonempty.
TEST(NonVacuityLocals, NexttimeDefersToTheSuffixNonVacuity) {
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"a"})}, *LvNexttime(Trig("a")), LocalContext{}));
}

// §F.5.3.3 edge case: over the empty word no letter can satisfy the abort
// condition b, so accept_on's no-abort alternative holds and the result reduces
// to the operand's non-vacuity -- nonvacuous for strong(s), vacuous for a
// trigger that cannot match.
TEST(NonVacuityLocals, AcceptOnOnTheEmptyWordFollowsTheOperand) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{}, *LvAcceptOn(BoolAtom("b"), Strong("s")), LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{}, *LvAcceptOn(BoolAtom("b"), Trig("a")), LocalContext{}));
}

// §F.5.3.3 edge case: the top-level disable iff rule shares accept_on's abort
// shape, so over the empty word it likewise reduces to the operand's
// non-vacuity.
TEST(NonVacuityLocals, TopLevelDisableIffOnTheEmptyWordFollowsTheOperand) {
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevelWithLocals(
      Word{}, *LvTopDisableIff(BoolAtom("b"), Strong("s")), LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesTopLevelWithLocals(
      Word{}, *LvTopDisableIff(BoolAtom("b"), Trig("a")), LocalContext{}));
}

}  // namespace
