#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_satisfaction_with_local_variables.h"
#include "elaborator/annex_f_satisfaction_without_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "elaborator/annex_f_vacuity.h"
#include "elaborator/annex_f_vacuity_local_variables.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

std::shared_ptr<const SequenceExpr> Sampling() {
  return SeqConcat(Bs("a"), SeqLocalVarSampling("v"));
}

std::shared_ptr<const LvProperty> Clean() {
  return LvUntil(LvNexttime(LvParen(LvStrong(Bs("a")))),
                 LvAcceptOn(BoolAtom("x"),
                            LvAnd(LvImplication(Bs("a"), LvStrong(Bs("b"))),
                                  LvNot(LvOr(LvWeak(SeqOr(Bs("c"), Bs("d"))),
                                             LvStrong(Bs("c")))))));
}

template <typename T, typename Equal>
bool SameOperand(const std::shared_ptr<const T>& lhs,
                 const std::shared_ptr<const T>& rhs, Equal equal) {
  if (!lhs || !rhs) {
    return lhs == rhs;
  }
  return equal(*lhs, *rhs);
}

bool LvEqual(const LvProperty& lhs, const LvProperty& rhs) {
  return lhs.kind == rhs.kind && lhs.local_var_type == rhs.local_var_type &&
         lhs.local_var_name == rhs.local_var_name &&
         SameOperand(lhs.sequence, rhs.sequence, SequenceExprEqual) &&
         SameOperand(lhs.boolean, rhs.boolean, BooleanExprEqual) &&
         SameOperand(lhs.lhs, rhs.lhs, LvEqual) &&
         SameOperand(lhs.rhs, rhs.rhs, LvEqual);
}

TEST(SatisfactionWithLocalVariables,
     APropertyInvolvesALocalByItsDeclarationOrItsSequences) {
  EXPECT_FALSE(LvPropertyInvolvesLocalVariables(*Clean()));
  EXPECT_TRUE(LvPropertyInvolvesLocalVariables(
      *LvLocalVarDecl("int", "v", LvStrong(Bs("a")))));
  EXPECT_TRUE(LvPropertyInvolvesLocalVariables(*LvUntil(
      LvStrong(Bs("a")),
      LvNot(LvNexttime(LvLocalVarDecl("int", "v", LvStrong(Bs("a"))))))));
  EXPECT_TRUE(LvPropertyInvolvesLocalVariables(*LvStrong(Sampling())));
  EXPECT_TRUE(LvPropertyInvolvesLocalVariables(
      *LvAnd(LvStrong(Bs("a")), LvImplication(Sampling(), LvStrong(Bs("b"))))));
  EXPECT_TRUE(LvPropertyInvolvesLocalVariables(
      *LvOr(LvStrong(Bs("a")), LvWeak(SeqLocalVarDecl("int", "v", Bs("a"))))));
}

TEST(SatisfactionWithLocalVariables,
     ATopLevelPropertyInvolvesALocalByItsDeclarationOrItsProperty) {
  EXPECT_FALSE(LvTopLevelPropertyInvolvesLocalVariables(
      *LvTopParen(LvTopDisableIff(BoolAtom("rst"), Clean()))));
  EXPECT_TRUE(LvTopLevelPropertyInvolvesLocalVariables(
      *LvTopLocalVarDecl("int", "v", LvTopProperty(Clean()))));
  EXPECT_TRUE(LvTopLevelPropertyInvolvesLocalVariables(
      *LvTopParen(LvTopDisableIff(BoolAtom("rst"), LvStrong(Sampling())))));
  EXPECT_TRUE(LvTopLevelPropertyInvolvesLocalVariables(
      *LvTopProperty(LvLocalVarDecl("int", "v", LvStrong(Bs("a"))))));
}

TEST(SatisfactionWithLocalVariables, TheRetractionInvertsTheEmbedding) {
  EXPECT_EQ(AsPropertyWithoutLocalVariables(*LvStrong(Sampling())), nullptr);
  EXPECT_EQ(AsPropertyWithoutLocalVariables(
                *LvNot(LvLocalVarDecl("int", "v", LvStrong(Bs("a"))))),
            nullptr);
  EXPECT_EQ(AsTopLevelPropertyWithoutLocalVariables(
                *LvTopLocalVarDecl("int", "v", LvTopProperty(Clean()))),
            nullptr);
  EXPECT_EQ(AsTopLevelPropertyWithoutLocalVariables(
                *LvTopDisableIff(BoolAtom("rst"), LvStrong(Sampling()))),
            nullptr);

  auto p = AsPropertyWithoutLocalVariables(*Clean());
  ASSERT_NE(p, nullptr);
  ASSERT_EQ(p->kind, PropertyExpr::Kind::kUntil);
  EXPECT_EQ(p->lhs->kind, PropertyExpr::Kind::kNexttime);
  EXPECT_EQ(p->lhs->lhs->kind, PropertyExpr::Kind::kParen);
  EXPECT_EQ(p->lhs->lhs->lhs->kind, PropertyExpr::Kind::kStrong);
  EXPECT_TRUE(SequenceExprEqual(*p->lhs->lhs->lhs->sequence, *Bs("a")));
  EXPECT_EQ(p->rhs->kind, PropertyExpr::Kind::kAcceptOn);
  EXPECT_TRUE(BooleanExprEqual(*p->rhs->boolean, *BoolAtom("x")));
  EXPECT_EQ(p->rhs->lhs->kind, PropertyExpr::Kind::kAnd);
  EXPECT_EQ(p->rhs->lhs->lhs->kind, PropertyExpr::Kind::kImplication);
  EXPECT_EQ(p->rhs->lhs->rhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(p->rhs->lhs->rhs->lhs->kind, PropertyExpr::Kind::kOr);
  EXPECT_EQ(p->rhs->lhs->rhs->lhs->lhs->kind, PropertyExpr::Kind::kWeak);
  EXPECT_EQ(p->rhs->lhs->rhs->lhs->rhs->kind, PropertyExpr::Kind::kStrong);
  EXPECT_TRUE(LvEqual(*AsPropertyWithLocalVariables(*p), *Clean()));

  auto top = AsTopLevelPropertyWithoutLocalVariables(
      *LvTopParen(LvTopDisableIff(BoolAtom("rst"), Clean())));
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->kind, TopLevelProperty::Kind::kParen);
  ASSERT_EQ(top->inner->kind, TopLevelProperty::Kind::kDisableIff);
  EXPECT_TRUE(
      BooleanExprEqual(*top->inner->disable_condition, *BoolAtom("rst")));
  EXPECT_TRUE(
      LvEqual(*AsPropertyWithLocalVariables(*top->inner->property), *Clean()));

  auto original = PropImplication(Bs("a"), PropNot(PropWeak(Bs("b"))));
  auto back =
      AsPropertyWithoutLocalVariables(*AsPropertyWithLocalVariables(*original));
  ASSERT_NE(back, nullptr);
  EXPECT_TRUE(LvEqual(*AsPropertyWithLocalVariables(*back),
                      *AsPropertyWithLocalVariables(*original)));
}

std::vector<Word> Words() {
  return {Word{},
          Word{A({"a"})},
          Word{A({"a"}), A({"b"})},
          Word{A({"a"}), A({"x"}), A({"c"})},
          Word{A({"x"}), A({"a", "d"})},
          Word{A({"a"}), LetterTop()},
          Word{LetterBottom(), A({"b"})}};
}
std::vector<LocalContext> Contexts() {
  return {LocalContext{}, LocalContext{{"v", A({"z"})}}};
}
std::vector<std::shared_ptr<const LvProperty>> Fragment() {
  return {Clean(),
          LvStrong(Bs("a")),
          LvWeak(SeqConcat(Bs("a"), Bs("b"))),
          LvImplication(Bs("a"), LvStrong(Bs("b"))),
          LvNot(LvWeak(SeqOr(Bs("a"), Bs("d")))),
          LvUntil(LvStrong(Bs("a")), LvNexttime(LvStrong(Bs("b")))),
          LvAcceptOn(BoolAtom("x"), LvStrong(SeqConcat(Bs("a"), Bs("b"))))};
}

TEST(SatisfactionWithLocalVariables, TheContextIsInertOnTheFragment) {
  std::set<bool> neutral;
  std::set<bool> vacuity;
  for (const auto& lv : Fragment()) {
    const auto kP = AsPropertyWithoutLocalVariables(*lv);
    ASSERT_NE(kP, nullptr);
    for (const Word& w : Words()) {
      const bool kNeutral = NeutrallySatisfies(w, *kP);
      const bool kVacuity = NonVacuouslyEvaluates(w, *kP);
      neutral.insert(kNeutral);
      vacuity.insert(kVacuity);
      for (const LocalContext& ctx : Contexts()) {
        EXPECT_EQ(NeutrallySatisfiesWithLocals(w, *lv, ctx), kNeutral);
        EXPECT_EQ(NonVacuouslyEvaluatesWithLocals(w, *lv, ctx), kVacuity);
      }
    }
  }
  EXPECT_EQ(neutral.size(), 2U);
  EXPECT_EQ(vacuity.size(), 2U);
}

TEST(SatisfactionWithLocalVariables, TheTopLevelVerdictsAreInertToTheContext) {
  std::set<bool> disabled;
  for (const auto& lv : Fragment()) {
    const auto kTop = LvTopParen(LvTopDisableIff(BoolAtom("d"), lv));
    const auto kT = AsTopLevelPropertyWithoutLocalVariables(*kTop);
    ASSERT_NE(kT, nullptr);
    for (const Word& w : Words()) {
      disabled.insert(IsDisabledTopLevel(w, *kT));
      for (const LocalContext& ctx : Contexts()) {
        EXPECT_EQ(PassesTopLevelWithLocals(w, *kTop, ctx),
                  PassesTopLevel(w, *kT));
        EXPECT_EQ(IsDisabledTopLevelWithLocals(w, *kTop, ctx),
                  IsDisabledTopLevel(w, *kT));
        EXPECT_EQ(FailsTopLevelWithLocals(w, *kTop, ctx),
                  FailsTopLevel(w, *kT));
        EXPECT_EQ(NonVacuouslyEvaluatesTopLevelWithLocals(w, *kTop, ctx),
                  NonVacuouslyEvaluatesTopLevel(w, *kT));
      }
    }
  }
  EXPECT_EQ(disabled.size(), 2U);
}

TEST(SatisfactionWithLocalVariables, OutsideTheFragmentTheNotionsAreItsOwn) {
  auto decl = LvLocalVarDecl("int", "v", LvStrong(Sampling()));
  EXPECT_EQ(AsPropertyWithoutLocalVariables(*decl), nullptr);
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"b"})}, *decl));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"x"})}, *decl));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"b"})}, *Sampling()));
}

}  // namespace
