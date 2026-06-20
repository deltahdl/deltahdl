#include <gtest/gtest.h>

#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// §F.5.2: w |== b iff |w| = 1 and w^0 |= b. A single letter that contains the
// proposition matches; a longer or empty word does not.
TEST(TightSatisfaction, BooleanNeedsExactlyOneSatisfyingLetter) {
  auto b = SeqBoolean(BoolAtom("a"));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"})}, *b));
  EXPECT_FALSE(TightlySatisfies(Word{}, *b));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"a"})}, *b));
  EXPECT_FALSE(TightlySatisfies(Word{A({"x"})}, *b));
}

// §F.5: the top letter T satisfies every Boolean and the bottom letter _|_
// satisfies none, regardless of the proposition.
TEST(TightSatisfaction, TopAndBottomLettersDecideEveryBoolean) {
  auto b = SeqBoolean(BoolAtom("a"));
  EXPECT_TRUE(TightlySatisfies(Word{LetterTop()}, *b));
  EXPECT_FALSE(TightlySatisfies(Word{LetterBottom()}, *b));
}

// §F.5.2: w |== (R) iff w |== R -- parentheses are transparent.
TEST(TightSatisfaction, ParenthesisIsTransparent) {
  auto paren = SeqParen(SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"})}, *paren));
  EXPECT_FALSE(TightlySatisfies(Word{A({"x"})}, *paren));
}

// §F.5.2: w |== (R1 ##1 R2) iff w splits into x y with x |== R1 and y |== R2.
TEST(TightSatisfaction, ConcatenationSplitsTheWord) {
  auto seq = SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"}), A({"b"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"b"}), A({"a"})}, *seq));
}

// §F.5.2: w |== (R1 ##0 R2) iff w = xyz with |y| = 1, xy |== R1 and yz |== R2;
// the operands overlap on one letter, so the fusion of two Booleans needs a
// single letter satisfying both.
TEST(TightSatisfaction, FusionOverlapsOnOneLetter) {
  auto seq = SeqFusion(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a", "b"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"b"})}, *seq));
}

// §F.5.2: w |== (R1 or R2) iff w |== R1 or w |== R2.
TEST(TightSatisfaction, OrTakesEitherOperand) {
  auto seq = SeqOr(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"})}, *seq));
  EXPECT_TRUE(TightlySatisfies(Word{A({"b"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"x"})}, *seq));
}

// §F.5.2: w |== (R1 intersect R2) iff w |== R1 and w |== R2.
TEST(TightSatisfaction, IntersectRequiresBothOperands) {
  auto seq = SeqIntersect(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a", "b"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"})}, *seq));
}

// §F.5.2: w |== first_match(R) iff w |== R and no proper prefix of w matches R
// -- only the shortest match is tight. a[*1:$] matches one or more letters, so
// first_match accepts only the single-letter word.
TEST(TightSatisfaction, FirstMatchKeepsOnlyTheShortestMatch) {
  auto seq = SeqFirstMatch(SeqUnboundedRepeat(SeqBoolean(BoolAtom("a"))));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"a"})}, *seq));
}

// §F.5.2: the no-shorter-match clause of first_match counts the empty prefix
// too. When R also matches the empty word (a or a[*0]), the empty word is the
// shortest match, so a one-letter word does not tightly satisfy first_match(R).
TEST(TightSatisfaction, FirstMatchRejectsWordWithMatchingEmptyPrefix) {
  auto a = SeqBoolean(BoolAtom("a"));
  auto seq = SeqFirstMatch(SeqOr(a, SeqNullRepeat(a)));
  EXPECT_TRUE(TightlySatisfies(Word{}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"})}, *seq));
}

// §F.5.2: w |== R[*0] iff |w| = 0.
TEST(TightSatisfaction, NullRepetitionMatchesOnlyTheEmptyWord) {
  auto seq = SeqNullRepeat(SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(TightlySatisfies(Word{}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"})}, *seq));
}

// §F.5.2: w |== R[*1:$] iff w is a concatenation of one or more words each
// matching R.
TEST(TightSatisfaction, UnboundedRepetitionConcatenatesMatches) {
  auto seq = SeqUnboundedRepeat(SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"})}, *seq));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"}), A({"a"}), A({"a"})}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{}, *seq));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"x"})}, *seq));
}

// §F.5.2: "If S is a clocked sequence, then w |== S iff w |== S'", where S' is
// the §F.5.1.1 rewrite. A clocked Boolean @(clk) a matches a single letter in
// which both clk and a hold, but not one where the clock is absent.
TEST(TightSatisfaction, ClockedSequenceEvaluatesViaRewrite) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"clk", "a"})}, *clocked));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"})}, *clocked));
}

// §F.5.2: an unclocked sequence is nondegenerate iff some nonempty word
// tightly satisfies it.
TEST(TightSatisfaction, NondegeneracyDetectsANonemptyWitness) {
  EXPECT_TRUE(IsNondegenerateSequence(*SeqBoolean(BoolAtom("a"))));
  EXPECT_TRUE(IsNondegenerateSequence(
      *SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")))));
}

// §F.5.2: a sequence that admits only the empty word (R[*0]) is degenerate.
TEST(TightSatisfaction, EmptyOnlySequenceIsDegenerate) {
  EXPECT_FALSE(
      IsNondegenerateSequence(*SeqNullRepeat(SeqBoolean(BoolAtom("a")))));
}

// §F.5.2: an intersection of sequences with incompatible lengths has no common
// word and so is degenerate. (a ##1 a) matches length two; a matches length
// one; their intersection matches nothing.
TEST(TightSatisfaction, ContradictoryIntersectionIsDegenerate) {
  auto two = SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("a")));
  auto one = SeqBoolean(BoolAtom("a"));
  EXPECT_FALSE(IsNondegenerateSequence(*SeqIntersect(two, one)));
}

// §F.5.2: a clocked sequence is nondegenerate iff its unclocked rewrite is.
TEST(TightSatisfaction, ClockedSequenceNondegeneracyUsesRewrite) {
  auto clocked = SeqClock(BoolAtom("clk"), SeqBoolean(BoolAtom("a")));
  EXPECT_TRUE(IsNondegenerateSequence(*clocked));
}

// §F.3.2 invokes "tightly satisfied by the empty word"; §F.5.2 makes that
// predicate concrete. R[*0] is satisfied by the empty word; a Boolean is not.
TEST(TightSatisfaction, EmptyWordSatisfactionIsDecidable) {
  EXPECT_TRUE(
      TightlySatisfiedByEmptyWord(*SeqNullRepeat(SeqBoolean(BoolAtom("a")))));
  EXPECT_FALSE(TightlySatisfiedByEmptyWord(*SeqBoolean(BoolAtom("a"))));
}

}  // namespace
