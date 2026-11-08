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
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "elaborator/annex_f_vacuity.h"
#include "elaborator/annex_f_vacuity_local_variables.h"

using namespace delta;

namespace {

Letter L(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

auto Samp(const std::string& name) { return SeqLocalVarSampling(name); }

auto Strong(const std::string& name) { return LvStrong(Bs(name)); }

auto Trig(const std::string& name) {
  return LvImplication(Bs(name), Strong("t"));
}

TEST(NonVacuityLocals, StrongAndWeakAreAlwaysNonvacuous) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *Strong("a"),
                                              LocalContext{}));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesWithLocals(Word{}, *Strong("a"), LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *LvWeak(Bs("a")),
                                              LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{}, *Strong("a"),
                                              LocalContext{{"u", L({"z"})}}));
}

TEST(NonVacuityLocals, ParenthesisIsTransparent) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"a"})}, *LvParen(Trig("a")), LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"})}, *LvParen(Trig("a")), LocalContext{}));
}

TEST(NonVacuityLocals, ImplicationNeedsTheTriggerToMatch) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *Trig("a"),
                                              LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *Trig("a"),
                                               LocalContext{}));
}

TEST(NonVacuityLocals, ImplicationThreadsAntecedentOutputContexts) {
  auto prop = LvImplication(Samp("v"), LvStrong(Samp("w")));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"}), L({"b"})}, *prop,
                                              LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{}, *prop, LocalContext{}));
}

TEST(NonVacuityLocals, DisjunctionIsNonvacuousWhenEitherSideIs) {
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"})}, *LvOr(Trig("a"), Trig("a")), LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"})}, *LvOr(Trig("a"), Strong("s")), LocalContext{}));
}

TEST(NonVacuityLocals, ConjunctionIsNonvacuousWhenEitherSideIs) {
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"})}, *LvAnd(Trig("a"), Trig("a")), LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"})}, *LvAnd(Strong("s"), Trig("a")), LocalContext{}));
}

TEST(NonVacuityLocals, NegationEvaluatesOnTheComplement) {
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{LetterBottom()}, *Trig("a"),
                                               LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{LetterBottom()}, *LvNot(Trig("a")), LocalContext{}));
}

TEST(NonVacuityLocals, NexttimeRequiresANonemptyWord) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"a"})}, *LvNexttime(Strong("b")), LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{}, *LvNexttime(Strong("b")),
                                               LocalContext{}));
}

TEST(NonVacuityLocals, UntilNeedsAnOperandToBecomeNonvacuous) {
  auto until = LvUntil(Trig("a"), Trig("a"));
  EXPECT_FALSE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *until, LocalContext{}));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *until, LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{L({"x"}), L({"a"})}, *until,
                                               LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"x"}), L({"a"})}, *LvUntil(Trig("a"), LvNot(Trig("a"))),
      LocalContext{}));
}

TEST(NonVacuityLocals, AcceptOnFollowsTheAbortShape) {
  auto good = LvAcceptOn(BoolAtom("b"), Strong("s"));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"s"})}, *good, LocalContext{}));
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"s"}), L({"b"})}, *good,
                                              LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{L({"b", "s"})}, *good,
                                               LocalContext{}));
  auto vacuous = LvAcceptOn(BoolAtom("b"), Trig("a"));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *vacuous,
                                               LocalContext{}));
}

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

TEST(NonVacuityLocals, EmptyContextEntryPoint) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *Strong("a")));
  EXPECT_EQ(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *Trig("a")),
            NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *Trig("a"),
                                            LocalContext{}));
}

TEST(NonVacuityLocals, PropertyDeclarationStripsTheNameFromTheContext) {
  auto body = Trig("a");
  auto decl = LvLocalVarDecl("int", "v", body);
  const LocalContext kCtx{{"v", L({"old"})}, {"u", L({"z"})}};

  EXPECT_EQ(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *decl, kCtx),
            NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *body,
                                            RemoveName(kCtx, "v")));
  EXPECT_EQ(NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *decl, kCtx),
            NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *body,
                                            RemoveName(kCtx, "v")));

  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *decl, kCtx));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *decl, kCtx));

  EXPECT_TRUE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *decl, LocalContext{}));

  auto nested =
      LvLocalVarDecl("int", "v", LvLocalVarDecl("int", "w", Trig("a")));
  EXPECT_TRUE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"a"})}, *nested, LocalContext{}));
  EXPECT_FALSE(
      NonVacuouslyEvaluatesWithLocals(Word{L({"x"})}, *nested, LocalContext{}));
}

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

TEST(NonVacuityLocals, UntilIsVacuousOverTheEmptyWord) {
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{}, *LvUntil(Trig("a"), Trig("a")), LocalContext{}));
}

TEST(NonVacuityLocals, NexttimeDefersToTheSuffixNonVacuity) {
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{L({"a"})}, *LvNexttime(Trig("a")), LocalContext{}));
}

TEST(NonVacuityLocals, AcceptOnOnTheEmptyWordFollowsTheOperand) {
  EXPECT_TRUE(NonVacuouslyEvaluatesWithLocals(
      Word{}, *LvAcceptOn(BoolAtom("b"), Strong("s")), LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesWithLocals(
      Word{}, *LvAcceptOn(BoolAtom("b"), Trig("a")), LocalContext{}));
}

TEST(NonVacuityLocals, TopLevelDisableIffOnTheEmptyWordFollowsTheOperand) {
  EXPECT_TRUE(NonVacuouslyEvaluatesTopLevelWithLocals(
      Word{}, *LvTopDisableIff(BoolAtom("b"), Strong("s")), LocalContext{}));
  EXPECT_FALSE(NonVacuouslyEvaluatesTopLevelWithLocals(
      Word{}, *LvTopDisableIff(BoolAtom("b"), Trig("a")), LocalContext{}));
}

std::shared_ptr<const LvProperty> DeclTrig() {
  return LvLocalVarDecl(
      "int", "v", LvImplication(SeqConcat(Bs("a"), Samp("v")), Strong("t")));
}

std::vector<LocalContext> Contexts() {
  return {LocalContext{}, LocalContext{{"v", L({"old"})}}};
}

struct OperandPair {
  std::shared_ptr<const LvProperty> lv1;
  std::shared_ptr<const LvProperty> lv2;
  std::shared_ptr<const PropertyExpr> p1;
  std::shared_ptr<const PropertyExpr> p2;
};
std::vector<OperandPair> OperandPairs() {
  const std::vector<std::shared_ptr<const LvProperty>> kOperands{
      Trig("a"), Strong("s"), LvNot(Trig("a"))};
  std::vector<OperandPair> out;
  for (const auto& lv1 : kOperands) {
    for (const auto& lv2 : kOperands) {
      out.push_back({lv1, lv2, AsPropertyWithoutLocalVariables(*lv1),
                     AsPropertyWithoutLocalVariables(*lv2)});
    }
  }
  return out;
}

TEST(NonVacuityLocals,
     DerivedRulesAgreeWithTheLocalFreeSemanticsOnTheFragment) {
  const std::vector<Word> kWords{Word{L({"x"}), L({"a", "t"})},
                                 Word{L({"a", "t"})},
                                 Word{L({"x"}), L({"x"})},
                                 Word{},
                                 Word{L({"a"})},
                                 Word{L({"b", "s"})}};
  const auto kB = BoolAtom("b");
  std::set<bool> seen;
  for (const OperandPair& o : OperandPairs()) {
    for (const Word& w : kWords) {
      for (const LocalContext& ctx : Contexts()) {
        const bool kIff =
            NonVacuouslyEvaluatesIffWithLocals(w, *o.lv1, *o.lv2, ctx);
        seen.insert(kIff);
        EXPECT_EQ(kIff, NonVacuouslyEvaluatesIff(w, *o.p1, *o.p2));
        EXPECT_EQ(
            NonVacuouslyEvaluatesImpliesWithLocals(w, *o.lv1, *o.lv2, ctx),
            NonVacuouslyEvaluatesImplies(w, *o.p1, *o.p2));
        EXPECT_EQ(NonVacuouslyEvaluatesSUntilWithLocals(w, *o.lv1, *o.lv2, ctx),
                  NonVacuouslyEvaluatesSUntil(w, *o.p1, *o.p2));
        EXPECT_EQ(NonVacuouslyEvaluatesAlwaysWithLocals(w, *o.lv1, ctx),
                  NonVacuouslyEvaluatesAlways(w, *o.p1));
        EXPECT_EQ(
            NonVacuouslyEvaluatesAlwaysRangeWithLocals(w, *o.lv1, 0, 1, ctx),
            NonVacuouslyEvaluatesAlwaysRange(w, *o.p1, 0, 1));
        EXPECT_EQ(
            NonVacuouslyEvaluatesSAlwaysRangeWithLocals(w, *o.lv1, 1, 2, ctx),
            NonVacuouslyEvaluatesSAlwaysRange(w, *o.p1, 1, 2));
        EXPECT_EQ(NonVacuouslyEvaluatesSEventuallyWithLocals(w, *o.lv1, ctx),
                  NonVacuouslyEvaluatesSEventually(w, *o.p1));
        EXPECT_EQ(NonVacuouslyEvaluatesEventuallyRangeWithLocals(w, *o.lv1, 0,
                                                                 1, ctx),
                  NonVacuouslyEvaluatesEventuallyRange(w, *o.p1, 0, 1));
        EXPECT_EQ(NonVacuouslyEvaluatesSEventuallyRangeWithLocals(w, *o.lv1, 1,
                                                                  2, ctx),
                  NonVacuouslyEvaluatesSEventuallyRange(w, *o.p1, 1, 2));
        EXPECT_EQ(NonVacuouslyEvaluatesRejectOnWithLocals(w, *kB, *o.lv1, ctx),
                  NonVacuouslyEvaluatesRejectOn(w, *kB, *o.p1));
      }
    }
  }
  EXPECT_EQ(seen.size(), 2U);
}

TEST(NonVacuityLocals, AlwaysReadsTheSamplingUnderTheDeclaration) {
  const Word kWord{L({"x"}), L({"a"}), L({"b", "t"})};
  for (const LocalContext& ctx : Contexts()) {
    EXPECT_TRUE(NonVacuouslyEvaluatesAlwaysWithLocals(kWord, *DeclTrig(), ctx));
    EXPECT_FALSE(NonVacuouslyEvaluatesAlwaysWithLocals(Word{L({"x"}), L({"x"})},
                                                       *DeclTrig(), ctx));
    EXPECT_FALSE(
        NonVacuouslyEvaluatesAlwaysWithLocals(kWord, *LvNot(DeclTrig()), ctx));
    EXPECT_TRUE(NonVacuouslyEvaluatesAlwaysRangeWithLocals(kWord, *DeclTrig(),
                                                           1, 1, ctx));
    EXPECT_FALSE(NonVacuouslyEvaluatesAlwaysRangeWithLocals(kWord, *DeclTrig(),
                                                            0, 0, ctx));
    EXPECT_EQ(NonVacuouslyEvaluatesSAlwaysRangeWithLocals(kWord, *DeclTrig(), 1,
                                                          2, ctx),
              NonVacuouslyEvaluatesAlwaysRangeWithLocals(kWord, *DeclTrig(), 1,
                                                         2, ctx));
  }
}

TEST(NonVacuityLocals, ImpliesReadsTheSamplingUnderTheDeclaration) {
  for (const LocalContext& ctx : Contexts()) {
    EXPECT_TRUE(NonVacuouslyEvaluatesImpliesWithLocals(
        Word{L({"a"}), L({"t"})}, *DeclTrig(), *Strong("s"), ctx));
    EXPECT_FALSE(NonVacuouslyEvaluatesImpliesWithLocals(
        Word{L({"a"}), L({"x"})}, *DeclTrig(), *Strong("s"), ctx));
    EXPECT_FALSE(NonVacuouslyEvaluatesImpliesWithLocals(
        Word{L({"x"}), L({"x"})}, *DeclTrig(), *Strong("s"), ctx));
    EXPECT_TRUE(NonVacuouslyEvaluatesIffWithLocals(
        Word{L({"a"}), L({"x"})}, *DeclTrig(), *DeclTrig(), ctx));
    EXPECT_FALSE(NonVacuouslyEvaluatesIffWithLocals(
        Word{L({"x"}), L({"a"})}, *DeclTrig(), *DeclTrig(), ctx));
  }
}

TEST(NonVacuityLocals, SEventuallyReadsTheSamplingUnderTheDeclaration) {
  const Word kWord{L({"x"}), L({"a"}), L({"b", "t"})};
  auto neg = LvNot(DeclTrig());
  for (const LocalContext& ctx : Contexts()) {
    EXPECT_TRUE(NonVacuouslyEvaluatesSEventuallyWithLocals(kWord, *neg, ctx));
    EXPECT_FALSE(
        NonVacuouslyEvaluatesSEventuallyWithLocals(kWord, *DeclTrig(), ctx));
    EXPECT_TRUE(
        NonVacuouslyEvaluatesEventuallyRangeWithLocals(kWord, *neg, 0, 1, ctx));
    EXPECT_FALSE(
        NonVacuouslyEvaluatesEventuallyRangeWithLocals(kWord, *neg, 0, 0, ctx));
    EXPECT_EQ(
        NonVacuouslyEvaluatesSEventuallyRangeWithLocals(kWord, *neg, 0, 2, ctx),
        NonVacuouslyEvaluatesEventuallyRangeWithLocals(kWord, *neg, 0, 2, ctx));
  }
}

TEST(NonVacuityLocals, SUntilSharesTheUntilRuleWithLocals) {
  auto until = LvUntil(DeclTrig(), LvNot(DeclTrig()));
  const std::vector<Word> kWords{Word{L({"x"}), L({"a"}), L({"b", "t"})},
                                 Word{L({"x"}), L({"x"})}, Word{L({"a"})},
                                 Word{}};
  for (const Word& w : kWords) {
    for (const LocalContext& ctx : Contexts()) {
      EXPECT_EQ(NonVacuouslyEvaluatesSUntilWithLocals(w, *DeclTrig(),
                                                      *LvNot(DeclTrig()), ctx),
                NonVacuouslyEvaluatesWithLocals(w, *until, ctx));
    }
  }
}

TEST(NonVacuityLocals, RejectOnSharesTheAbortShapeWithLocals) {
  auto p = LvStrong(SeqConcat(Bs("s"), Samp("v")));
  for (const LocalContext& ctx : Contexts()) {
    EXPECT_TRUE(NonVacuouslyEvaluatesRejectOnWithLocals(
        Word{L({"s"}), L({"x"}), L({"b"})}, *BoolAtom("b"), *p, ctx));
    EXPECT_FALSE(NonVacuouslyEvaluatesRejectOnWithLocals(
        Word{L({"b", "s"})}, *BoolAtom("b"), *p, ctx));
    EXPECT_TRUE(NonVacuouslyEvaluatesRejectOnWithLocals(
        Word{L({"x"})}, *BoolAtom("b"), *p, ctx));
  }
}

}  // namespace
