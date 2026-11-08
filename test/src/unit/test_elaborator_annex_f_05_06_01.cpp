#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables_clocked.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto Bool(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

auto Samp(const std::string& name) { return SeqLocalVarSampling(name); }

TEST(NeutralSatisfactionLocals, StrongUsesFourWayRelation) {
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"})}, *LvStrong(Bool("a")),
                                           LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(
      Word{A({"b"})}, *LvStrong(Bool("a")), LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"x"})}, *LvStrong(Samp("v")),
                                           LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{}, *LvStrong(Samp("v")),
                                            LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"x"})}, *LvStrong(Samp("v")),
                                           LocalContext{{"u", A({"z"})}}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      Word{A({"x"})}, *LvStrong(SeqLocalVarDecl("int", "v", Samp("v"))),
      LocalContext{}));
}

TEST(NeutralSatisfactionLocals, WeakIsVacuousOnEmptyWordAndCompletesPrefixes) {
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{}, *LvWeak(Bool("a")), LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{}, *LvStrong(Bool("a")),
                                            LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"})}, *LvWeak(Bool("a")),
                                           LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"b"})}, *LvWeak(Bool("a")),
                                            LocalContext{}));
}

TEST(NeutralSatisfactionLocals, NotEvaluatesAgainstTheComplementWord) {
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      Word{A({"b"})}, *LvNot(LvStrong(Bool("a"))), LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(
      Word{A({"a"})}, *LvNot(LvStrong(Bool("a"))), LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      Word{LetterTop()}, *LvNot(LvStrong(Bool("a"))), LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(
      Word{LetterBottom()}, *LvNot(LvStrong(Bool("a"))), LocalContext{}));
}

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

TEST(NeutralSatisfactionLocals, NexttimeAdvancesOneLetter) {
  auto prop = LvNexttime(LvStrong(Bool("b")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"b"})}, *prop,
                                           LocalContext{}));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *prop, LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{}, *prop, LocalContext{}));
}

TEST(NeutralSatisfactionLocals, UntilHoldsUntilSecondOperand) {
  auto prop = LvUntil(LvStrong(Bool("a")), LvStrong(Bool("b")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"b"})}, *prop,
                                           LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"c"})}, *prop,
                                            LocalContext{}));
}

TEST(NeutralSatisfactionLocals, AcceptOnPassesOnAbortPrefix) {
  auto prop = LvAcceptOn(BoolAtom("b"), LvStrong(Bool("a")));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *prop, LocalContext{}));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"b"})}, *prop, LocalContext{}));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"c"})}, *prop, LocalContext{}));
}

TEST(NeutralSatisfactionLocals, ParenIsTransparent) {
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(
      Word{A({"a"})}, *LvParen(LvStrong(Bool("a"))), LocalContext{}));
}

TEST(NeutralSatisfactionLocals, ImplicationThreadsAntecedentOutputs) {
  auto holds = LvImplication(Samp("v"), LvStrong(Samp("w")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"b"})}, *holds,
                                           LocalContext{}));
  auto fails = LvImplication(Samp("v"), LvStrong(Bool("z")));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *fails, LocalContext{}));
  auto vacuous = LvImplication(Bool("q"), LvStrong(Bool("z")));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *vacuous, LocalContext{}));
}

TEST(NeutralSatisfactionLocals, PropertyDeclarationScopesTheName) {
  auto decl = LvLocalVarDecl("int", "v", LvStrong(Samp("v")));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"x"})}, *decl, LocalContext{}));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"x"})}, *decl,
                                           LocalContext{{"v", A({"old"})}}));
  auto decl_fail = LvLocalVarDecl("int", "v", LvStrong(Bool("a")));
  EXPECT_FALSE(
      NeutrallySatisfiesWithLocals(Word{A({"b"})}, *decl_fail, LocalContext{}));
  auto nested = LvLocalVarDecl("int", "v",
                               LvLocalVarDecl("int", "w", LvStrong(Samp("w"))));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"x"})}, *nested, LocalContext{}));
}

TEST(NeutralSatisfactionLocals, EmptyContextEntryPoint) {
  auto prop = LvStrong(Bool("a"));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"})}, *prop));
  EXPECT_EQ(
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *prop),
      NeutrallySatisfiesWithLocals(Word{A({"a"})}, *prop, LocalContext{}));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"b"})}, *prop));
}

TEST(NeutralSatisfactionLocals, TopLevelBarePropertyPassesAndFails) {
  auto top = LvTopProperty(LvStrong(Bool("a")));
  EXPECT_TRUE(PassesTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  EXPECT_FALSE(
      IsDisabledTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  EXPECT_FALSE(FailsTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  EXPECT_FALSE(PassesTopLevelWithLocals(Word{A({"b"})}, *top, LocalContext{}));
  EXPECT_FALSE(
      IsDisabledTopLevelWithLocals(Word{A({"b"})}, *top, LocalContext{}));
  EXPECT_TRUE(FailsTopLevelWithLocals(Word{A({"b"})}, *top, LocalContext{}));
}

TEST(NeutralSatisfactionLocals, TopLevelDisableIffPassesAndDisables) {
  auto top = LvTopDisableIff(BoolAtom("g"), LvStrong(Bool("a")));
  EXPECT_TRUE(PassesTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  EXPECT_FALSE(
      IsDisabledTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  EXPECT_FALSE(PassesTopLevelWithLocals(Word{A({"g"})}, *top, LocalContext{}));
  EXPECT_TRUE(
      IsDisabledTopLevelWithLocals(Word{A({"g"})}, *top, LocalContext{}));
  EXPECT_FALSE(FailsTopLevelWithLocals(Word{A({"g"})}, *top, LocalContext{}));
  EXPECT_FALSE(
      PassesTopLevelWithLocals(Word{A({"g"})}, *top, LocalContext{}) &&
      IsDisabledTopLevelWithLocals(Word{A({"g"})}, *top, LocalContext{}));
}

TEST(NeutralSatisfactionLocals, TopLevelParenIsTransparent) {
  auto top = LvTopParen(LvTopProperty(LvStrong(Bool("a"))));
  EXPECT_TRUE(PassesTopLevelWithLocals(Word{A({"a"})}, *top, LocalContext{}));
  auto guarded =
      LvTopParen(LvTopDisableIff(BoolAtom("g"), LvStrong(Bool("a"))));
  EXPECT_TRUE(
      IsDisabledTopLevelWithLocals(Word{A({"g"})}, *guarded, LocalContext{}));
}

TEST(NeutralSatisfactionLocals, TopLevelDeclarationScopesTheName) {
  auto top = LvTopLocalVarDecl("int", "v", LvTopProperty(LvStrong(Samp("v"))));
  EXPECT_TRUE(PassesTopLevelWithLocals(Word{A({"x"})}, *top, LocalContext{}));
  EXPECT_TRUE(PassesTopLevelWithLocals(Word{A({"x"})}, *top,
                                       LocalContext{{"v", A({"old"})}}));
  auto top_fail =
      LvTopLocalVarDecl("int", "v", LvTopProperty(LvStrong(Bool("a"))));
  EXPECT_TRUE(
      FailsTopLevelWithLocals(Word{A({"b"})}, *top_fail, LocalContext{}));
  auto top_disable = LvTopLocalVarDecl(
      "int", "v", LvTopDisableIff(BoolAtom("g"), LvStrong(Bool("a"))));
  EXPECT_TRUE(IsDisabledTopLevelWithLocals(Word{A({"g"})}, *top_disable,
                                           LocalContext{}));
}

TEST(NeutralSatisfactionLocals, UntilHoldsWhenFirstOperandPersists) {
  auto prop = LvUntil(LvStrong(Bool("a")), LvStrong(Bool("z")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"a"})}, *prop,
                                           LocalContext{}));
}

TEST(NeutralSatisfactionLocals, UntilIsVacuousOverEmptyWord) {
  auto prop = LvUntil(LvStrong(Bool("a")), LvStrong(Bool("z")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{}, *prop, LocalContext{}));
}

TEST(NeutralSatisfactionLocals, AcceptOnFailsWhenAbortPrefixDoesNotSatisfy) {
  auto prop = LvAcceptOn(BoolAtom("b"), LvStrong(Bool("a")));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"c"}), A({"b"})}, *prop,
                                            LocalContext{}));
}

TEST(NeutralSatisfactionLocals,
     TopLevelDisableIffFailsWhenNeitherPassNorDisabled) {
  auto top = LvTopDisableIff(BoolAtom("g"), LvStrong(Bool("z")));
  const Word kWord{A({"c"}), A({"g"})};
  EXPECT_FALSE(PassesTopLevelWithLocals(kWord, *top, LocalContext{}));
  EXPECT_FALSE(IsDisabledTopLevelWithLocals(kWord, *top, LocalContext{}));
  EXPECT_TRUE(FailsTopLevelWithLocals(kWord, *top, LocalContext{}));
}

TEST(NeutralSatisfactionLocals, ImplicationIsVacuousOverEmptyWord) {
  auto prop = LvImplication(Samp("v"), LvStrong(Samp("w")));
  EXPECT_TRUE(NeutrallySatisfiesWithLocals(Word{}, *prop, LocalContext{}));
}

TEST(NeutralSatisfactionLocals,
     ImplicationFailsWhenConsequentFailsAtLaterMatch) {
  auto prop = LvImplication(SeqUnboundedRepeat(Bool("a")),
                            LvNexttime(LvStrong(Bool("a"))));
  EXPECT_FALSE(NeutrallySatisfiesWithLocals(Word{A({"a"}), A({"a"})}, *prop,
                                            LocalContext{}));
}

TEST(NeutralSatisfactionLocals, OrSatisfiedByRightOperandAlone) {
  auto disj = LvOr(LvStrong(Bool("a")), LvStrong(Bool("b")));
  EXPECT_TRUE(
      NeutrallySatisfiesWithLocals(Word{A({"b"})}, *disj, LocalContext{}));
}

TEST(NeutralSatisfactionLocals,
     TopLevelDisableIffFailsWhenUnguardedPropertyFails) {
  auto top = LvTopDisableIff(BoolAtom("g"), LvStrong(Bool("a")));
  const Word kWord{A({"c"})};
  EXPECT_FALSE(PassesTopLevelWithLocals(kWord, *top, LocalContext{}));
  EXPECT_FALSE(IsDisabledTopLevelWithLocals(kWord, *top, LocalContext{}));
  EXPECT_TRUE(FailsTopLevelWithLocals(kWord, *top, LocalContext{}));
}

using Activation = AssertionStatement::Activation;
using Role = AssertionStatement::Role;

std::shared_ptr<const ClockedProperty> ClockedSampling() {
  return ClkClock(BoolAtom("clk"), ClkStrong(SeqConcat(Bool("a"), Samp("v"))));
}

TEST(NeutralSatisfactionLocals, ClockedPropertyIsDecidedByItsRewrite) {
  auto tick = ClkClock(BoolAtom("clk"), ClkStrong(Samp("v")));
  const std::vector<LocalContext> kContexts{LocalContext{},
                                            LocalContext{{"v", A({"old"})}}};
  for (const LocalContext& ctx : kContexts) {
    EXPECT_TRUE(NeutrallySatisfiesClockedPropertyWithLocals(
        Word{A({"x"}), A({"clk"})}, *tick, ctx));
    EXPECT_FALSE(NeutrallySatisfiesClockedPropertyWithLocals(Word{A({"x"})},
                                                             *tick, ctx));
    EXPECT_TRUE(NeutrallySatisfiesClockedPropertyWithLocals(
        Word{A({"a", "clk"}), A({"x"}), A({"b", "clk"})}, *ClockedSampling(),
        ctx));
    EXPECT_FALSE(NeutrallySatisfiesClockedPropertyWithLocals(
        Word{A({"a", "clk"}), A({"x"})}, *ClockedSampling(), ctx));
  }
  auto plain = ClkClock(BoolAtom("clk"), ClkStrong(Bool("a")));
  const std::vector<Word> kWords{Word{A({"a", "clk"})}, Word{A({"x", "clk"})},
                                 Word{A({"x"}), A({"a", "clk"})}};
  for (const Word& w : kWords) {
    EXPECT_EQ(
        NeutrallySatisfiesClockedPropertyWithLocals(w, *plain, LocalContext{}),
        NeutrallySatisfiesClockedProperty(w, *plain));
  }
}

TEST(NeutralSatisfactionLocals, ClockedTopLevelFormsReduceToTheirTForms) {
  auto u = LvClockedTopLocalVarDecl(
      "int", "v",
      LvClockedTopParen(LvClockedTopDisableIff(
          BoolAtom("rst"), ClkClock(BoolAtom("clk"), ClkStrong(Samp("v"))))));
  auto t = UnclockTopLevelWithLocals(*u, BoolTrue());
  ASSERT_EQ(t->kind, LvTopLevelProperty::Kind::kLocalVarDecl);
  EXPECT_EQ(t->local_var_name, "v");
  ASSERT_EQ(t->inner->kind, LvTopLevelProperty::Kind::kParen);
  ASSERT_EQ(t->inner->inner->kind, LvTopLevelProperty::Kind::kDisableIff);
  EXPECT_TRUE(
      BooleanExprEqual(*t->inner->inner->disable_condition, *BoolAtom("rst")));
  const LocalContext kBound{{"v", A({"old"})}};
  EXPECT_TRUE(
      PassesTopLevelClockedWithLocals(Word{A({"x"}), A({"clk"})}, *u, kBound));
  EXPECT_TRUE(NeutrallySatisfiesTopLevelClockedWithLocals(
      Word{A({"x"}), A({"clk"})}, *u, kBound));
  EXPECT_FALSE(IsDisabledTopLevelClockedWithLocals(Word{A({"x"}), A({"clk"})},
                                                   *u, kBound));
  EXPECT_TRUE(IsDisabledTopLevelClockedWithLocals(Word{A({"rst"})}, *u,
                                                  LocalContext{}));
  EXPECT_TRUE(
      DisablesTopLevelClockedWithLocals(Word{A({"rst"})}, *u, LocalContext{}));
  EXPECT_FALSE(
      PassesTopLevelClockedWithLocals(Word{A({"rst"})}, *u, LocalContext{}));
  EXPECT_FALSE(
      FailsTopLevelClockedWithLocals(Word{A({"rst"})}, *u, LocalContext{}));
  EXPECT_TRUE(FailsTopLevelClockedWithLocals(Word{A({"x"})}, *u, kBound));
  EXPECT_FALSE(PassesTopLevelClockedWithLocals(Word{A({"x"})}, *u, kBound));
  EXPECT_FALSE(IsDisabledTopLevelClockedWithLocals(Word{A({"x"})}, *u, kBound));
}

TEST(NeutralSatisfactionLocals, AssertionsThreadLocalsThroughTheirBodies) {
  auto body = LvClockedTopLocalVarDecl(
      "int", "v",
      LvClockedTopProperty(ClkStrong(SeqConcat(Bool("a"), Samp("v")))));
  auto initial = LvAssertionWithClock(Activation::kInitial, Role::kAssert,
                                      BoolAtom("clk"), body);
  EXPECT_TRUE(NeutrallySatisfiesAssertionWithLocals(
      Word{A({"a", "clk"}), A({"b", "clk"})}, *BoolTrue(), *initial));
  EXPECT_FALSE(NeutrallySatisfiesAssertionWithLocals(Word{A({"a", "clk"})},
                                                     *BoolTrue(), *initial));
  EXPECT_FALSE(NeutrallySatisfiesAssertionWithLocals(
      Word{A({"x", "clk"}), A({"a", "clk"}), A({"b", "clk"})}, *BoolTrue(),
      *initial));
  auto cover = LvAssertionWithClock(
      Activation::kAlways, Role::kCover, BoolAtom("clk"),
      LvClockedTopProperty(ClkStrong(SeqConcat(Bool("a"), Samp("v")))));
  EXPECT_TRUE(NeutrallySatisfiesAssertionWithLocals(
      Word{A({"x", "clk"}), A({"a", "clk"}), A({"b", "clk"})}, *BoolTrue(),
      *cover));
  EXPECT_FALSE(NeutrallySatisfiesAssertionWithLocals(
      Word{A({"x", "clk"}), A({"x", "clk"})}, *BoolTrue(), *cover));
  auto u = LvAssertionWithClockedTop(
      Activation::kInitial, Role::kAssert,
      LvClockedTopLocalVarDecl("int", "v",
                               LvClockedTopProperty(ClockedSampling())));
  EXPECT_TRUE(NeutrallySatisfiesAssertionWithLocals(
      Word{A({"a", "clk"}), A({"b", "clk"})}, *BoolTrue(), *u));
  EXPECT_FALSE(NeutrallySatisfiesAssertionWithLocals(Word{A({"a", "clk"})},
                                                     *BoolTrue(), *u));
  EXPECT_TRUE(NeutrallySatisfiesAssertionWithLocals(Word{A({"a", "clk"})},
                                                    *BoolAtom("en"), *u));
}

TEST(NeutralSatisfactionLocals,
     AssertionsWithoutLocalsAgreeWithTheLocalFreeSemantics) {
  const auto kAThenB = SeqConcat(Bool("a"), Bool("b"));
  auto q = ClkClock(BoolAtom("clk"), ClkStrong(kAThenB));
  const std::vector<Word> kWords{
      Word{A({"a", "clk"}), A({"b", "clk"})},
      Word{A({"a", "clk"}), A({"x"}), A({"b", "clk"})},
      Word{A({"x", "clk"}), A({"a", "clk"}), A({"b", "clk"})},
      Word{A({"x", "clk"})}, Word{}};
  for (Activation activation : {Activation::kAlways, Activation::kInitial}) {
    for (Role role : {Role::kAssert, Role::kCover}) {
      auto lv_u =
          LvAssertionWithClockedTop(activation, role, LvClockedTopProperty(q));
      auto plain_u =
          AssertionWithClockedTop(activation, role, ClockedTopProperty(q));
      auto lv_t =
          LvAssertionWithClock(activation, role, BoolAtom("clk"),
                               LvClockedTopProperty(ClkStrong(kAThenB)));
      auto plain_t = AssertionWithClock(activation, role, BoolAtom("clk"),
                                        TopProperty(PropStrong(kAThenB)));
      for (const Word& w : kWords) {
        EXPECT_EQ(NeutrallySatisfiesAssertionWithLocals(w, *BoolTrue(), *lv_u),
                  NeutrallySatisfiesAssertion(w, *BoolTrue(), *plain_u));
        EXPECT_EQ(NeutrallySatisfiesAssertionWithLocals(w, *BoolTrue(), *lv_t),
                  NeutrallySatisfiesAssertion(w, *BoolTrue(), *plain_t));
      }
    }
  }
}

}  // namespace
