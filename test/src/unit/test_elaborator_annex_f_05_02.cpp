#include <gtest/gtest.h>

#include <set>
#include <string>
#include <utility>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

TEST(TightSatisfaction, BooleanNeedsExactlyOneSatisfyingLetter) {
  auto b = SeqBoolean(BoolAtom("a"));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"})}, *b));
  EXPECT_FALSE(TightlySatisfies(Word{}, *b));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"a"})}, *b));
  EXPECT_FALSE(TightlySatisfies(Word{A({"x"})}, *b));
}

TEST(TightSatisfaction, TopAndBottomLettersDecideEveryBoolean) {
  auto b = SeqBoolean(BoolAtom("a"));
  EXPECT_TRUE(TightlySatisfies(Word{LetterTop()}, *b));
  EXPECT_FALSE(TightlySatisfies(Word{LetterBottom()}, *b));
}

TEST(TightSatisfaction, ParenthesisIsTransparent) {
  auto paren = SeqParen(SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"})}, *paren));
  EXPECT_FALSE(TightlySatisfies(Word{A({"x"})}, *paren));
}

TEST(TightSatisfaction, ConcatenationSplitsTheWord) {
  auto seq = SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"}), A({"b"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"b"}), A({"a"})}, *seq));
}

TEST(TightSatisfaction, FusionOverlapsOnOneLetter) {
  auto seq = SeqFusion(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a", "b"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"b"})}, *seq));
}

TEST(TightSatisfaction, OrTakesEitherOperand) {
  auto seq = SeqOr(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"})}, *seq));
  EXPECT_TRUE(TightlySatisfies(Word{A({"b"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"x"})}, *seq));
}

TEST(TightSatisfaction, IntersectRequiresBothOperands) {
  auto seq = SeqIntersect(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a", "b"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"})}, *seq));
}

TEST(TightSatisfaction, FirstMatchKeepsOnlyTheShortestMatch) {
  auto seq = SeqFirstMatch(SeqUnboundedRepeat(SeqBoolean(BoolAtom("a"))));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"a"})}, *seq));
}

TEST(TightSatisfaction, FirstMatchRejectsWordWithMatchingEmptyPrefix) {
  auto a = SeqBoolean(BoolAtom("a"));
  auto seq = SeqFirstMatch(SeqOr(a, SeqNullRepeat(a)));
  EXPECT_TRUE(TightlySatisfies(Word{}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"})}, *seq));
}

TEST(TightSatisfaction,
     DISABLED_FirstMatchJudgesAShorterMatchOnTheComplementedPrefix) {
  auto a = SeqBoolean(BoolAtom("a"));
  auto seq = SeqFirstMatch(SeqOr(a, SeqConcat(a, SeqBoolean(BoolAtom("b")))));
  EXPECT_TRUE(TightlySatisfies(Word{LetterTop(), A({"b"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"b"})}, *seq));
}

TEST(TightSatisfaction, NullRepetitionMatchesOnlyTheEmptyWord) {
  auto seq = SeqNullRepeat(SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(TightlySatisfies(Word{}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"})}, *seq));
}

TEST(TightSatisfaction, UnboundedRepetitionConcatenatesMatches) {
  auto seq = SeqUnboundedRepeat(SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"})}, *seq));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"}), A({"a"}), A({"a"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"x"})}, *seq));
}

TEST(TightSatisfaction, ClockedSequenceEvaluatesViaRewrite) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"clk", "a"})}, *clocked));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"})}, *clocked));
}

TEST(TightSatisfaction, ClockedSequenceAbsorbsIdleLettersBeforeItsTick) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(TightlySatisfies(Word{A({}), A({}), A({"clk", "a"})}, *clocked));
  EXPECT_FALSE(TightlySatisfies(Word{A({"clk", "a"}), A({})}, *clocked));
  EXPECT_FALSE(TightlySatisfies(Word{A({}), A({"a"})}, *clocked));
}

TEST(TightSatisfaction, NondegeneracyDetectsANonemptyWitness) {
  EXPECT_TRUE(IsNondegenerateSequence(*SeqBoolean(BoolAtom("a"))));
  EXPECT_TRUE(IsNondegenerateSequence(
      *SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")))));
}

TEST(TightSatisfaction, EmptyOnlySequenceIsDegenerate) {
  EXPECT_FALSE(
      IsNondegenerateSequence(*SeqNullRepeat(SeqBoolean(BoolAtom("a")))));
}

TEST(TightSatisfaction, ContradictoryIntersectionIsDegenerate) {
  auto two = SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("a")));
  auto one = SeqBoolean(BoolAtom("a"));
  EXPECT_FALSE(IsNondegenerateSequence(*SeqIntersect(two, one)));
}

TEST(TightSatisfaction, ClockedSequenceNondegeneracyUsesRewrite) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(IsNondegenerateSequence(*clocked));
}

TEST(TightSatisfaction, ClockedSequenceWhoseRewriteIsDegenerateIsDegenerate) {
  auto a = SeqBoolean(BoolAtom("a"));
  EXPECT_FALSE(
      IsNondegenerateSequence(*SeqClock(BoolAtom("clk"), SeqNullRepeat(a))));
  EXPECT_FALSE(IsNondegenerateSequence(
      *SeqClock(BoolAtom("clk"), SeqIntersect(SeqNullRepeat(a), a))));
}

TEST(TightSatisfaction, ClockedLengthClashIsNondegenerateThroughTopLetters) {
  auto a = SeqBoolean(BoolAtom("a"));
  auto clocked = SeqClock(BoolAtom("clk"), SeqIntersect(SeqConcat(a, a), a));
  EXPECT_TRUE(IsNondegenerateSequence(*clocked));
  EXPECT_TRUE(TightlySatisfies(Word{LetterTop(), LetterTop()}, *clocked));
  EXPECT_FALSE(
      TightlySatisfies(Word{A({"clk", "a"}), A({"clk", "a"})}, *clocked));
}

TEST(TightSatisfaction, EmptyWordSatisfactionIsDecidable) {
  EXPECT_TRUE(
      TightlySatisfiedByEmptyWord(*SeqNullRepeat(SeqBoolean(BoolAtom("a")))));
  EXPECT_FALSE(TightlySatisfiedByEmptyWord(*SeqBoolean(BoolAtom("a"))));
}

}  // namespace
