#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_local_variable_flow.h"
#include "elaborator/annex_f_sequence_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "helpers_annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

TEST(TightSatisfactionLocals, ContextDomainAndRestrictions) {
  const LocalContext kCtx{{"v", A({"x"})}, {"w", A({"y"})}};
  EXPECT_EQ(ContextDomain(kCtx), (NameSet{"v", "w"}));
  EXPECT_TRUE(LocalContextEqual(RestrictContext(kCtx, {"v"}),
                                LocalContext{{"v", A({"x"})}}));
  EXPECT_TRUE(
      LocalContextEqual(RemoveName(kCtx, "v"), LocalContext{{"w", A({"y"})}}));
  EXPECT_TRUE(LocalContextEqual(RestrictToName(kCtx, "w"),
                                LocalContext{{"w", A({"y"})}}));
  EXPECT_TRUE(
      LocalContextEqual(RestrictToName(kCtx, "absent"), LocalContext{}));
}

TEST(TightSatisfactionLocals, LetterEquality) {
  EXPECT_TRUE(LetterEqual(A({"x"}), A({"x"})));
  EXPECT_FALSE(LetterEqual(A({"x"}), A({"y"})));
  EXPECT_TRUE(LetterEqual(LetterTop(), LetterTop()));
  EXPECT_FALSE(LetterEqual(LetterTop(), LetterBottom()));
  EXPECT_FALSE(LetterEqual(LetterTop(), A({"x"})));
}

TEST(TightSatisfactionLocals, BooleanPreservesContextAndNeedsOneLetter) {
  const LocalContext kInput{{"w", A({"y"})}};
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"a"})}, *Bool("a"), kInput), {kInput}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"x"})}, *Bool("a"), kInput).empty());
  EXPECT_TRUE(TightSatisfactionOutputs(Word{}, *Bool("a"), kInput).empty());
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"a"}), A({"a"})}, *Bool("a"), kInput)
          .empty());
}

TEST(TightSatisfactionLocals, SamplingBindsObservedValue) {
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *Samp("v"), LocalContext{}),
      {LocalContext{{"v", A({"x"})}}}));
  EXPECT_TRUE(
      SameContexts(TightSatisfactionOutputs(Word{A({"x"})}, *Samp("v"),
                                            LocalContext{{"w", A({"y"})}}),
                   {LocalContext{{"w", A({"y"})}, {"v", A({"x"})}}}));
  EXPECT_TRUE(
      SameContexts(TightSatisfactionOutputs(Word{A({"x"})}, *Samp("v"),
                                            LocalContext{{"v", A({"old"})}}),
                   {LocalContext{{"v", A({"x"})}}}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{}, *Samp("v"), LocalContext{}).empty());
}

TEST(TightSatisfactionLocals, LocalDeclScopesTheDeclaredName) {
  auto decl = SeqLocalVarDecl("int", "v", Samp("v"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *decl, LocalContext{}),
      {LocalContext{}}));
  EXPECT_TRUE(
      SameContexts(TightSatisfactionOutputs(Word{A({"x"})}, *decl,
                                            LocalContext{{"v", A({"old"})}}),
                   {LocalContext{{"v", A({"old"})}}}));
  EXPECT_TRUE(
      SameContexts(TightSatisfactionOutputs(Word{A({"x"})}, *decl,
                                            LocalContext{{"w", A({"y"})}}),
                   {LocalContext{{"w", A({"y"})}}}));
}

TEST(TightSatisfactionLocals, ParenthesisIsTransparent) {
  EXPECT_TRUE(
      SameContexts(TightSatisfactionOutputs(
                       Word{A({"x"})}, *SeqParen(Samp("v")), LocalContext{}),
                   {LocalContext{{"v", A({"x"})}}}));
}

TEST(TightSatisfactionLocals, ConcatThreadsContextAcrossSplit) {
  auto seq = SeqConcat(Samp("v"), Samp("w"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"}), A({"y"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"x"})}, {"w", A({"y"})}}}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"x"})}, *seq, LocalContext{}).empty());
}

TEST(TightSatisfactionLocals, FusionOverlapsOneLetterAndThreadsContext) {
  auto seq = SeqFusion(Samp("v"), Bool("a"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"a"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"a"})}}}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"a"}), A({"a"})}, *seq, LocalContext{})
          .empty());
}

TEST(TightSatisfactionLocals, OrRestrictsToFlowDomain) {
  auto disagree = SeqOr(Samp("v"), Samp("w"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *disagree, LocalContext{}),
      {LocalContext{}}));
  auto agree = SeqOr(Samp("v"), Samp("v"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *agree, LocalContext{}),
      {LocalContext{{"v", A({"x"})}}}));
}

TEST(TightSatisfactionLocals, IntersectKeepsDistinctNamesFromBothOperands) {
  auto seq = SeqIntersect(Samp("v"), Samp("w"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"x"})}, {"w", A({"x"})}}}));
}

TEST(TightSatisfactionLocals, IntersectBlocksCommonlySampledName) {
  auto seq = SeqIntersect(Samp("v"), Samp("v"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *seq, LocalContext{}),
      {LocalContext{}}));
}

TEST(TightSatisfactionLocals, FirstMatchRejectsWhenAProperPrefixMatches) {
  auto seq = SeqFirstMatch(SeqUnboundedRepeat(Samp("v")));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"x"})}}}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"x"}), A({"y"})}, *seq, LocalContext{})
          .empty());
}

TEST(TightSatisfactionLocals, NullRepeatMatchesEmptyWordAndPreservesContext) {
  const LocalContext kInput{{"w", A({"y"})}};
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{}, *SeqNullRepeat(Samp("v")), kInput),
      {kInput}));
  EXPECT_TRUE(TightSatisfactionOutputs(Word{A({"x"})},
                                       *SeqNullRepeat(Samp("v")), kInput)
                  .empty());
}

TEST(TightSatisfactionLocals, UnboundedRepeatChainsContextThroughPieces) {
  auto seq = SeqUnboundedRepeat(Samp("v"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"x"})}}}));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"}), A({"y"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"y"})}}}));
}

TEST(TightSatisfactionLocals, FourWayPredicateAcceptsOnlyYieldedContexts) {
  EXPECT_TRUE(TightlySatisfiesWithLocals(Word{A({"x"})}, *Samp("v"),
                                         LocalContext{},
                                         LocalContext{{"v", A({"x"})}}));
  EXPECT_FALSE(TightlySatisfiesWithLocals(Word{A({"x"})}, *Samp("v"),
                                          LocalContext{},
                                          LocalContext{{"v", A({"y"})}}));
  EXPECT_FALSE(TightlySatisfiesWithLocals(Word{A({"x"})}, *Samp("v"),
                                          LocalContext{}, LocalContext{}));
}

TEST(TightSatisfactionLocals, OutputDomainEqualsFlowOfInputDomain) {
  const Letter kX = A({"x"});
  const Letter kY = A({"y"});
  const std::vector<std::pair<std::shared_ptr<const SequenceExpr>, Word>>
      kCases{
          {Samp("v"), Word{kX}},
          {SeqConcat(Samp("v"), Samp("w")), Word{kX, kY}},
          {SeqOr(Samp("v"), Samp("w")), Word{kX}},
          {SeqIntersect(Samp("v"), Samp("w")), Word{kX}},
          {SeqLocalVarDecl("int", "v", Samp("v")), Word{kX}},
  };
  const LocalContext kInput{{"u", A({"z"})}};
  for (const auto& item : kCases) {
    const NameSet kExpected = FlowLocals(ContextDomain(kInput), *item.first);
    const auto kOutputs =
        TightSatisfactionOutputs(item.second, *item.first, kInput);
    EXPECT_FALSE(kOutputs.empty());
    for (const LocalContext& out : kOutputs) {
      EXPECT_EQ(ContextDomain(out), kExpected);
    }
  }
}

TEST(TightSatisfactionLocals, ClockedSequenceMatchesItsUnclockedRewrite) {
  auto clocked = SeqClock(BoolAtom("clk"), Samp("v"));
  auto unclocked = RewriteClockedSequence(*clocked);
  const std::vector<Letter> kAlphabet{LetterTop(), A({}), A({"clk"})};
  std::vector<Word> words{Word{}};
  for (const Letter& l0 : kAlphabet) {
    words.push_back(Word{l0});
    for (const Letter& l1 : kAlphabet) {
      words.push_back(Word{l0, l1});
      for (const Letter& l2 : kAlphabet) {
        words.push_back(Word{l0, l1, l2});
      }
    }
  }
  bool saw_match = false;
  for (const Word& w : words) {
    auto via_clock = TightSatisfactionOutputs(w, *clocked, LocalContext{});
    auto via_rewrite = TightSatisfactionOutputs(w, *unclocked, LocalContext{});
    EXPECT_TRUE(SameContexts(via_clock, via_rewrite));
    saw_match = saw_match || !via_clock.empty();
  }
  EXPECT_TRUE(saw_match);
}

TEST(TightSatisfactionLocals, NondegeneracyReflectsNonemptyMatch) {
  EXPECT_TRUE(IsNondegenerateSequenceWithLocals(*Samp("v")));
  EXPECT_TRUE(IsNondegenerateSequenceWithLocals(*Bool("a")));
  EXPECT_TRUE(
      IsNondegenerateSequenceWithLocals(*SeqClock(BoolAtom("clk"), Samp("v"))));
  auto incompatible = SeqIntersect(Bool("a"), SeqConcat(Bool("a"), Bool("a")));
  EXPECT_FALSE(IsNondegenerateSequenceWithLocals(*incompatible));
  EXPECT_FALSE(IsNondegenerateSequenceWithLocals(*SeqNullRepeat(Bool("a"))));
}

TEST(TightSatisfactionLocals, SamplingOverUnknownLetterStillBinds) {
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{LetterTop()}, *Samp("v"), LocalContext{}),
      {LocalContext{{"v", LetterTop()}}}));
  EXPECT_TRUE(SameContexts(TightSatisfactionOutputs(Word{LetterBottom()},
                                                    *Samp("v"), LocalContext{}),
                           {LocalContext{{"v", LetterBottom()}}}));
}

TEST(TightSatisfactionLocals, BooleanMatchesTopRejectsBottom) {
  const LocalContext kInput{{"w", A({"y"})}};
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{LetterTop()}, *Bool("a"), kInput),
      {kInput}));
  EXPECT_TRUE(TightSatisfactionOutputs(Word{LetterBottom()}, *Bool("a"), kInput)
                  .empty());
}

TEST(TightSatisfactionLocals, ConcatAdmitsEmptyLeftOperand) {
  auto seq = SeqConcat(SeqNullRepeat(Bool("a")), Bool("b"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"b"})}, *seq, LocalContext{}),
      {LocalContext{}}));
}

TEST(TightSatisfactionLocals, FusionRejectsEmptyWord) {
  auto seq = SeqFusion(Bool("a"), Bool("b"));
  EXPECT_TRUE(TightSatisfactionOutputs(Word{}, *seq, LocalContext{}).empty());
}

TEST(TightSatisfactionLocals, OrYieldsNothingWhenNoBranchMatches) {
  auto seq = SeqOr(Bool("a"), Bool("b"));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"c"})}, *seq, LocalContext{}).empty());
}

TEST(TightSatisfactionLocals, IntersectYieldsNothingForIncompatibleLengths) {
  auto seq = SeqIntersect(Bool("a"), SeqConcat(Bool("a"), Bool("a")));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"a"})}, *seq, LocalContext{}).empty());
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"a"}), A({"a"})}, *seq, LocalContext{})
          .empty());
}

TEST(TightSatisfactionLocals, UnboundedRepeatRejectsEmptyWord) {
  auto seq = SeqUnboundedRepeat(Bool("a"));
  EXPECT_TRUE(TightSatisfactionOutputs(Word{}, *seq, LocalContext{}).empty());
}

}  // namespace
