#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_satisfaction_without_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "elaborator/annex_f_vacuity.h"
#include "elaborator/annex_f_vacuity_local_variables.h"

using namespace delta;

// §F.5.3 heads the three notions of satisfaction -- neutral (§F.5.3.1), weak
// and strong by finite words (§F.5.3.2) and vacuity (§F.5.3.3) -- and its
// title fixes their common scope: satisfaction without local variables, the
// assumption §F.5.3.1 opens with for every property, sequence and unclocked
// property fragment. §F.5.6 restates the same three notions with local
// variables, each as the rules of §F.5.3 with the understanding that the
// underlying properties may carry them. The cases observe the scope -- which
// sequences, properties, top-level properties and assertion statements of the
// §F.3.2 grammar involve a local variable -- and that on every input within it
// the §F.5.6 relations, entered from the empty context, agree with the §F.5.3
// ones, while on an input outside it they part.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// ( int v; a ##1 (1, v = e) ): a sequence that declares and samples a local.
std::shared_ptr<const SequenceExpr> WithLocal() {
  return SeqLocalVarDecl("int", "v",
                         SeqConcat(Bs("a"), SeqLocalVarSampling("v")));
}

// A property, top-level property and assertion statement in §F.5.3's scope,
// and the same three with a local variable sequence in place of one operand.
std::shared_ptr<const PropertyExpr> Clean() {
  return PropAnd(PropImplication(Bs("a"), PropStrong(Bs("b"))),
                 PropNot(PropWeak(SeqOr(Bs("c"), Bs("d")))));
}
std::shared_ptr<const PropertyExpr> Tainted() {
  return PropAnd(PropImplication(Bs("a"), PropStrong(Bs("b"))),
                 PropNot(PropWeak(SeqOr(Bs("c"), WithLocal()))));
}

// §F.5.3: a sequence involves a local variable iff a declaration or a sampling
// form occurs in it, at any depth; the other §F.3.2 sequence forms, a clock
// included, do not by themselves.
TEST(SatisfactionWithoutLocalVariables, ASequenceInvolvesALocalByItsForms) {
  EXPECT_FALSE(SequenceInvolvesLocalVariables(*Bs("a")));
  EXPECT_FALSE(SequenceInvolvesLocalVariables(*SeqClock(
      BoolAtom("clk"), SeqFirstMatch(SeqIntersect(
                           SeqUnboundedRepeat(Bs("a")),
                           SeqFusion(Bs("b"), SeqNullRepeat(Bs("c"))))))));
  EXPECT_TRUE(SequenceInvolvesLocalVariables(*SeqLocalVarSampling("v")));
  EXPECT_TRUE(
      SequenceInvolvesLocalVariables(*SeqLocalVarDecl("int", "v", Bs("a"))));
  EXPECT_TRUE(SequenceInvolvesLocalVariables(*SeqClock(
      BoolAtom("clk"),
      SeqParen(SeqConcat(Bs("a"), SeqOr(Bs("b"), SeqLocalVarSampling("v")))))));
  // The right operand alone is enough, and so is the left.
  EXPECT_TRUE(SequenceInvolvesLocalVariables(*SeqConcat(Bs("a"), WithLocal())));
  EXPECT_TRUE(SequenceInvolvesLocalVariables(*SeqConcat(WithLocal(), Bs("a"))));
}

// §F.5.3: the property productions have no local variable form, so a property
// involves a local variable iff a sequence operand does, under any operator
// and at any depth -- here the right operand of an or under weak under not
// under and.
TEST(SatisfactionWithoutLocalVariables,
     APropertyInvolvesALocalThroughItsSequences) {
  EXPECT_FALSE(PropertyInvolvesLocalVariables(*Clean()));
  EXPECT_TRUE(PropertyInvolvesLocalVariables(*Tainted()));
  EXPECT_TRUE(PropertyInvolvesLocalVariables(*PropStrong(WithLocal())));
  EXPECT_TRUE(PropertyInvolvesLocalVariables(*PropWeak(WithLocal())));
  EXPECT_TRUE(PropertyInvolvesLocalVariables(
      *PropImplication(WithLocal(), PropStrong(Bs("b")))));
  EXPECT_TRUE(PropertyInvolvesLocalVariables(*PropUntil(
      PropStrong(Bs("a")), PropNexttime(PropParen(PropAcceptOn(
                               BoolAtom("x"), PropStrong(WithLocal())))))));
  EXPECT_FALSE(PropertyInvolvesLocalVariables(*PropUntil(
      PropStrong(Bs("a")), PropNexttime(PropParen(PropAcceptOn(
                               BoolAtom("x"), PropStrong(Bs("b"))))))));
}

// §F.5.3: a top-level property involves a local variable iff the property it
// carries does, through a disable iff guard or a parenthesis alike; the guard
// condition is a Boolean and holds none.
TEST(SatisfactionWithoutLocalVariables, ATopLevelPropertyFollowsItsProperty) {
  EXPECT_FALSE(TopLevelPropertyInvolvesLocalVariables(*TopProperty(Clean())));
  EXPECT_TRUE(TopLevelPropertyInvolvesLocalVariables(*TopProperty(Tainted())));
  EXPECT_FALSE(TopLevelPropertyInvolvesLocalVariables(
      *TopDisableIff(BoolAtom("rst"), Clean())));
  EXPECT_TRUE(TopLevelPropertyInvolvesLocalVariables(
      *TopDisableIff(BoolAtom("rst"), Tainted())));
  EXPECT_FALSE(TopLevelPropertyInvolvesLocalVariables(
      *TopParen(TopParen(TopProperty(Clean())))));
  EXPECT_TRUE(TopLevelPropertyInvolvesLocalVariables(
      *TopParen(TopParen(TopProperty(Tainted())))));
}

// §F.5.3: a clocked property and a clocked top-level property involve a local
// variable on the same terms, the clock and abort conditions being Booleans.
TEST(SatisfactionWithoutLocalVariables, AClockedPropertyFollowsItsSequences) {
  auto clean =
      ClkClock(BoolAtom("clk"),
               ClkUntil(ClkBoolean(BoolAtom("a")),
                        ClkSyncAcceptOn(BoolAtom("x"), ClkStrong(Bs("b")))));
  auto tainted = ClkClock(
      BoolAtom("clk"),
      ClkUntil(ClkBoolean(BoolAtom("a")),
               ClkSyncAcceptOn(BoolAtom("x"), ClkStrong(WithLocal()))));
  EXPECT_FALSE(ClockedPropertyInvolvesLocalVariables(*clean));
  EXPECT_TRUE(ClockedPropertyInvolvesLocalVariables(*tainted));
  EXPECT_TRUE(ClockedPropertyInvolvesLocalVariables(
      *ClkImplication(WithLocal(), ClkBoolean(BoolAtom("a")))));
  EXPECT_FALSE(ClockedTopLevelPropertyInvolvesLocalVariables(
      *ClockedTopParen(ClockedTopDisableIff(BoolAtom("rst"), clean))));
  EXPECT_TRUE(ClockedTopLevelPropertyInvolvesLocalVariables(
      *ClockedTopParen(ClockedTopDisableIff(BoolAtom("rst"), tainted))));
}

// §F.5.3: an assertion statement involves a local variable iff its body does,
// in the @( c ) T shape and in the U shape alike; the activation, the role and
// the clock c change nothing.
TEST(SatisfactionWithoutLocalVariables, AnAssertionStatementFollowsItsBody) {
  using Activation = AssertionStatement::Activation;
  using Role = AssertionStatement::Role;
  EXPECT_FALSE(AssertionInvolvesLocalVariables(
      *AssertionWithClock(Activation::kAlways, Role::kAssert, BoolAtom("clk"),
                          TopProperty(Clean()))));
  EXPECT_TRUE(AssertionInvolvesLocalVariables(
      *AssertionWithClock(Activation::kInitial, Role::kCover, BoolAtom("clk"),
                          TopProperty(Tainted()))));
  EXPECT_FALSE(AssertionInvolvesLocalVariables(*AssertionWithClockedTop(
      Activation::kAlways, Role::kAssume,
      ClockedTopProperty(ClkClock(BoolAtom("clk"), ClkStrong(Bs("a")))))));
  EXPECT_TRUE(AssertionInvolvesLocalVariables(*AssertionWithClockedTop(
      Activation::kAlways, Role::kAssume,
      ClockedTopProperty(ClkClock(BoolAtom("clk"), ClkStrong(WithLocal()))))));
}

// §F.5.3 is the fragment of §F.5.6 without local variables: the embedding of a
// §F.5.3 property into the §F.5.6 model keeps each operator, sequence operand
// and Boolean, adds no declaration form, and goes through a top-level
// property's guard and parenthesis.
TEST(SatisfactionWithoutLocalVariables, TheEmbeddingKeepsTheShape) {
  auto lv = AsPropertyWithLocalVariables(*Clean());
  ASSERT_EQ(lv->kind, LvProperty::Kind::kAnd);
  ASSERT_NE(lv->lhs, nullptr);
  ASSERT_NE(lv->rhs, nullptr);
  EXPECT_EQ(lv->lhs->kind, LvProperty::Kind::kImplication);
  EXPECT_TRUE(SequenceExprEqual(*lv->lhs->sequence, *Bs("a")));
  ASSERT_NE(lv->lhs->lhs, nullptr);
  EXPECT_EQ(lv->lhs->lhs->kind, LvProperty::Kind::kStrong);
  EXPECT_TRUE(SequenceExprEqual(*lv->lhs->lhs->sequence, *Bs("b")));
  EXPECT_EQ(lv->rhs->kind, LvProperty::Kind::kNot);
  ASSERT_NE(lv->rhs->lhs, nullptr);
  EXPECT_EQ(lv->rhs->lhs->kind, LvProperty::Kind::kWeak);
  EXPECT_TRUE(
      SequenceExprEqual(*lv->rhs->lhs->sequence, *SeqOr(Bs("c"), Bs("d"))));
  EXPECT_TRUE(lv->local_var_name.empty());

  auto accept = AsPropertyWithLocalVariables(
      *PropUntil(PropNexttime(PropParen(PropStrong(Bs("a")))),
                 PropAcceptOn(BoolAtom("x"),
                              PropOr(PropWeak(Bs("b")), PropStrong(Bs("c"))))));
  ASSERT_EQ(accept->kind, LvProperty::Kind::kUntil);
  EXPECT_EQ(accept->lhs->kind, LvProperty::Kind::kNexttime);
  EXPECT_EQ(accept->lhs->lhs->kind, LvProperty::Kind::kParen);
  EXPECT_EQ(accept->lhs->lhs->lhs->kind, LvProperty::Kind::kStrong);
  EXPECT_EQ(accept->rhs->kind, LvProperty::Kind::kAcceptOn);
  EXPECT_TRUE(BooleanExprEqual(*accept->rhs->boolean, *BoolAtom("x")));
  EXPECT_EQ(accept->rhs->lhs->kind, LvProperty::Kind::kOr);
  EXPECT_EQ(accept->rhs->lhs->lhs->kind, LvProperty::Kind::kWeak);
  EXPECT_EQ(accept->rhs->lhs->rhs->kind, LvProperty::Kind::kStrong);

  auto top = AsTopLevelPropertyWithLocalVariables(
      *TopParen(TopDisableIff(BoolAtom("rst"), PropStrong(Bs("a")))));
  ASSERT_EQ(top->kind, LvTopLevelProperty::Kind::kParen);
  ASSERT_NE(top->inner, nullptr);
  EXPECT_EQ(top->inner->kind, LvTopLevelProperty::Kind::kDisableIff);
  EXPECT_TRUE(
      BooleanExprEqual(*top->inner->disable_condition, *BoolAtom("rst")));
  ASSERT_NE(top->inner->property, nullptr);
  EXPECT_EQ(top->inner->property->kind, LvProperty::Kind::kStrong);
  EXPECT_EQ(AsTopLevelPropertyWithLocalVariables(*TopProperty(Clean()))->kind,
            LvTopLevelProperty::Kind::kProperty);
}

// The words the agreement is observed on: enough shapes that each operator of
// Clean() decides differently on some of them.
std::vector<Word> Words() {
  return {Word{A({"a"}), A({"b"})},
          Word{A({"a"}), A({"x"})},
          Word{A({"a", "c"}), A({"b"})},
          Word{A({"d"}), A({"a"}), A({"b"})},
          Word{A({"x"})},
          Word{A({"a"}), A({"b"}), A({"c"}), A({"d"})}};
}

// The properties the agreement is observed on: every §F.5.3.1 operator
// appears, and each is within §F.5.3's scope.
std::vector<std::shared_ptr<const PropertyExpr>> Properties() {
  return {Clean(),
          PropStrong(SeqConcat(Bs("a"), Bs("b"))),
          PropWeak(SeqConcat(Bs("a"), Bs("b"))),
          PropNot(PropStrong(Bs("a"))),
          PropImplication(Bs("a"), PropStrong(Bs("b"))),
          PropOr(PropStrong(Bs("x")), PropStrong(Bs("d"))),
          PropNexttime(PropStrong(Bs("b"))),
          PropUntil(PropWeak(Bs("a")), PropStrong(Bs("b"))),
          PropAcceptOn(BoolAtom("c"), PropStrong(SeqConcat(Bs("b"), Bs("x")))),
          PropParen(PropAnd(PropStrong(Bs("a")), PropWeak(Bs("d"))))};
}

// §F.5.6.1 gives neutral satisfaction as the rules of §F.5.3.1 with local
// variables understood to be allowed, so on a property that involves none
// the two agree, §F.5.6.1 entered from the empty context, on every word --
// and the verdicts are not all one way.
TEST(SatisfactionWithoutLocalVariables, NeutralSatisfactionAgreesWithF563) {
  std::set<bool> verdicts;
  for (const auto& property : Properties()) {
    ASSERT_FALSE(PropertyInvolvesLocalVariables(*property));
    auto lv = AsPropertyWithLocalVariables(*property);
    for (const Word& word : Words()) {
      const bool kWithout = NeutrallySatisfies(word, *property);
      EXPECT_EQ(kWithout, NeutrallySatisfiesWithLocals(word, *lv));
      EXPECT_EQ(kWithout,
                NeutrallySatisfiesWithLocals(word, *lv, LocalContext{}));
      verdicts.insert(kWithout);
    }
  }
  EXPECT_EQ(verdicts.size(), 2U);
}

// The same agreement at the top level: satisfaction, disabling and the
// pass/disabled/fail trichotomy of §F.5.3.1 are those of §F.5.6.1 on a
// top-level property without local variables, through a disable iff guard
// and a parenthesis.
TEST(SatisfactionWithoutLocalVariables, TopLevelVerdictsAgreeWithF563) {
  std::vector<std::shared_ptr<const TopLevelProperty>> tops;
  for (const auto& property : Properties()) {
    tops.push_back(TopProperty(property));
    tops.push_back(TopDisableIff(BoolAtom("d"), property));
    tops.push_back(TopParen(TopDisableIff(BoolAtom("x"), property)));
  }
  std::set<bool> disabled;
  for (const auto& top : tops) {
    ASSERT_FALSE(TopLevelPropertyInvolvesLocalVariables(*top));
    auto lv = AsTopLevelPropertyWithLocalVariables(*top);
    for (const Word& word : Words()) {
      EXPECT_EQ(
          NeutrallySatisfiesTopLevel(word, *top),
          NeutrallySatisfiesTopLevelWithLocals(word, *lv, LocalContext{}));
      EXPECT_EQ(DisablesTopLevel(word, *top),
                DisablesTopLevelWithLocals(word, *lv, LocalContext{}));
      EXPECT_EQ(PassesTopLevel(word, *top),
                PassesTopLevelWithLocals(word, *lv, LocalContext{}));
      EXPECT_EQ(IsDisabledTopLevel(word, *top),
                IsDisabledTopLevelWithLocals(word, *lv, LocalContext{}));
      EXPECT_EQ(FailsTopLevel(word, *top),
                FailsTopLevelWithLocals(word, *lv, LocalContext{}));
      disabled.insert(IsDisabledTopLevel(word, *top));
    }
  }
  EXPECT_EQ(disabled.size(), 2U);
}

// §F.5.6.3 gives vacuity as the definition of §F.5.3.3 with local variables
// understood to be allowed, so non-vacuity and nonvacuous satisfaction agree
// on every property and top-level property without local variables.
TEST(SatisfactionWithoutLocalVariables, VacuityAgreesWithF563) {
  std::set<bool> verdicts;
  for (const auto& property : Properties()) {
    auto lv = AsPropertyWithLocalVariables(*property);
    for (const Word& word : Words()) {
      const bool kWithout = NonVacuouslyEvaluates(word, *property);
      EXPECT_EQ(kWithout, NonVacuouslyEvaluatesWithLocals(word, *lv));
      EXPECT_EQ(SatisfiesNonVacuously(word, *property),
                SatisfiesNonVacuouslyWithLocals(word, *lv, LocalContext{}));
      verdicts.insert(kWithout);
    }
    auto top = TopDisableIff(BoolAtom("d"), property);
    auto lv_top = AsTopLevelPropertyWithLocalVariables(*top);
    for (const Word& word : Words()) {
      EXPECT_EQ(NonVacuouslyEvaluatesTopLevel(word, *top),
                NonVacuouslyEvaluatesTopLevelWithLocals(word, *lv_top,
                                                        LocalContext{}));
      EXPECT_EQ(SatisfiesTopLevelNonVacuously(word, *top),
                SatisfiesTopLevelNonVacuouslyWithLocals(word, *lv_top,
                                                        LocalContext{}));
    }
  }
  EXPECT_EQ(verdicts.size(), 2U);
}

// Outside §F.5.3's scope the two part: a property whose sequence samples a
// local is one §F.5.6.1 decides through the four-way relation, where the
// sampling ( 1, v = e ) matches a letter and binds v, while §F.5.3.1 knows no
// such form and finds no match. The disagreement is what the scope excludes.
TEST(SatisfactionWithoutLocalVariables, OutsideTheScopeTheRelationsPart) {
  auto sampling = PropStrong(SeqConcat(Bs("a"), SeqLocalVarSampling("v")));
  ASSERT_TRUE(PropertyInvolvesLocalVariables(*sampling));
  const Word kWord{A({"a"}), A({"b"})};
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      kWord, *AsPropertyWithLocalVariables(*sampling)));
  EXPECT_FALSE(NeutrallySatisfies(kWord, *sampling));
}

}  // namespace
