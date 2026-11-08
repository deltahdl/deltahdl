#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>
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

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

std::shared_ptr<const SequenceExpr> WithLocal() {
  return SeqLocalVarDecl("int", "v",
                         SeqConcat(Bs("a"), SeqLocalVarSampling("v")));
}

std::shared_ptr<const PropertyExpr> Clean() {
  return PropAnd(PropImplication(Bs("a"), PropStrong(Bs("b"))),
                 PropNot(PropWeak(SeqOr(Bs("c"), Bs("d")))));
}
std::shared_ptr<const PropertyExpr> Tainted() {
  return PropAnd(PropImplication(Bs("a"), PropStrong(Bs("b"))),
                 PropNot(PropWeak(SeqOr(Bs("c"), WithLocal()))));
}

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
  EXPECT_TRUE(SequenceInvolvesLocalVariables(*SeqConcat(Bs("a"), WithLocal())));
  EXPECT_TRUE(SequenceInvolvesLocalVariables(*SeqConcat(WithLocal(), Bs("a"))));
}

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

std::vector<Word> Words() {
  return {Word{A({"a"}), A({"b"})},
          Word{A({"a"}), A({"x"})},
          Word{A({"a", "c"}), A({"b"})},
          Word{A({"d"}), A({"a"}), A({"b"})},
          Word{A({"x"})},
          Word{A({"a"}), A({"b"}), A({"c"}), A({"d"})}};
}

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

TEST(SatisfactionWithoutLocalVariables,
     NeutralSatisfactionAgreesWithTheLocalVariableSemantics) {
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

TEST(SatisfactionWithoutLocalVariables,
     TopLevelVerdictsAgreeWithTheLocalVariableSemantics) {
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

TEST(SatisfactionWithoutLocalVariables,
     VacuityAgreesWithTheLocalVariableSemantics) {
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

TEST(SatisfactionWithoutLocalVariables, OutsideTheScopeTheRelationsPart) {
  auto sampling = PropStrong(SeqConcat(Bs("a"), SeqLocalVarSampling("v")));
  ASSERT_TRUE(PropertyInvolvesLocalVariables(*sampling));
  const Word kWord{A({"a"}), A({"b"})};
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      kWord, *AsPropertyWithLocalVariables(*sampling)));
  EXPECT_FALSE(NeutrallySatisfies(kWord, *sampling));
}

}  // namespace
