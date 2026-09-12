#include <gtest/gtest.h>

#include <cstddef>
#include <set>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_sequence_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

// §F.3.4 opens the derived forms with one convention of its own: a
// composition of the operators ##1 and or is written without internal
// parentheses, because both are associative. Every §F.3.2 form is binary and
// parenthesized, so a derived form such as (R1 ##1 1[*m-1:n-1] ##1 R2) or
// (R[*0] or R[*1:$]) stands for either of two trees, and the convention holds
// only because §F.5's satisfaction relations give the two trees the same
// words. These cases check that, for the sequence ##1 and or of §F.5.2, for
// the same sequences under a clock through the §F.5.1.1 rewrite, and for the
// property or of §F.5.3.1: over every word up to a bounded length, the
// left-grouped and the right-grouped composition are satisfied by the same
// words, and those words are the ones the ungrouped composition names.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto BoolSeq(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// Every word over `alphabet` of length at most `max_length`, the empty word
// included, so that a grouping which differs on any word up to that length is
// caught.
std::vector<Word> WordsUpTo(const std::vector<Letter>& alphabet,
                            std::size_t max_length) {
  std::vector<Word> words{Word{}};
  std::size_t begin = 0;
  for (std::size_t length = 1; length <= max_length; ++length) {
    std::size_t end = words.size();
    for (std::size_t i = begin; i < end; ++i) {
      for (const auto& letter : alphabet) {
        Word next = words[i];
        next.push_back(letter);
        words.push_back(next);
      }
    }
    begin = end;
  }
  return words;
}

std::vector<Letter> UnclockedAlphabet() {
  return {A({}), A({"a"}), A({"b"}), A({"c"})};
}

// The number of words in `words` that tightly satisfy both groupings, after
// checking that no word satisfies one and not the other.
std::size_t CountAgreeingMatches(const std::vector<Word>& words,
                                 const SequenceExpr& left_grouped,
                                 const SequenceExpr& right_grouped) {
  std::size_t matches = 0;
  for (const auto& word : words) {
    bool left = TightlySatisfies(word, left_grouped);
    EXPECT_EQ(left, TightlySatisfies(word, right_grouped));
    if (left) ++matches;
  }
  return matches;
}

// (a ##1 b[*1:$]) ##1 c and a ##1 (b[*1:$] ##1 c) are tightly satisfied by
// the same words, which for length up to four are a b c and a b b c: the
// middle operand has no fixed length, so a split made at the wrong operand
// boundary would differ between the two trees.
TEST(DerivedFormConventions, SequenceConcatenationGroupsEitherWay) {
  auto middle = SeqUnboundedRepeat(BoolSeq("b"));
  auto left = SeqConcat(SeqConcat(BoolSeq("a"), middle), BoolSeq("c"));
  auto right = SeqConcat(BoolSeq("a"), SeqConcat(middle, BoolSeq("c")));
  auto words = WordsUpTo(UnclockedAlphabet(), 4);
  EXPECT_EQ(CountAgreeingMatches(words, *left, *right), 2u);
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"}), A({"b"}), A({"c"})}, *left));
  EXPECT_TRUE(
      TightlySatisfies(Word{A({"a"}), A({"b"}), A({"b"}), A({"c"})}, *right));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"c"})}, *left));
}

// (a or b[*1:$]) or c and a or (b[*1:$] or c) are tightly satisfied by the
// same words: a, c, and each run of b up to the bound, six words in all.
TEST(DerivedFormConventions, SequenceOrGroupsEitherWay) {
  auto middle = SeqUnboundedRepeat(BoolSeq("b"));
  auto left = SeqOr(SeqOr(BoolSeq("a"), middle), BoolSeq("c"));
  auto right = SeqOr(BoolSeq("a"), SeqOr(middle, BoolSeq("c")));
  auto words = WordsUpTo(UnclockedAlphabet(), 4);
  EXPECT_EQ(CountAgreeingMatches(words, *left, *right), 6u);
  EXPECT_TRUE(TightlySatisfies(Word{A({"c"})}, *left));
  EXPECT_TRUE(TightlySatisfies(Word{A({"b"}), A({"b"})}, *right));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"c"})}, *left));
}

// The convention survives the §F.5.1.1 clock rewrite, which recurses into
// each operand of ##1 and or and so keeps whichever tree it was given: under
// the clock k, both trees of a ##1 b ##1 c are satisfied by a b c on three
// clock letters and by the same word with one unclocked letter before any of
// the three, four words up to length four. A clock letter carrying none of a,
// b and c fits nowhere.
TEST(DerivedFormConventions, ClockRewriteKeepsEitherGrouping) {
  auto left = SeqConcat(SeqConcat(BoolSeq("a"), BoolSeq("b")), BoolSeq("c"));
  auto right = SeqConcat(BoolSeq("a"), SeqConcat(BoolSeq("b"), BoolSeq("c")));
  auto clock = BoolAtom("k");
  auto left_clocked = RewriteSequenceUnderClock(*left, clock);
  auto right_clocked = RewriteSequenceUnderClock(*right, clock);
  std::vector<Letter> alphabet = {A({}), A({"k"}), A({"k", "a"}), A({"k", "b"}),
                                  A({"k", "c"})};
  auto words = WordsUpTo(alphabet, 4);
  EXPECT_EQ(CountAgreeingMatches(words, *left_clocked, *right_clocked), 4u);
  EXPECT_TRUE(TightlySatisfies(
      Word{A({"k", "a"}), A({}), A({"k", "b"}), A({"k", "c"})}, *left_clocked));
  EXPECT_FALSE(TightlySatisfies(
      Word{A({"k", "a"}), A({"k"}), A({"k", "b"}), A({"k", "c"})},
      *right_clocked));
}

// The property or of §F.5.3.1 is associative as well: (p or q) or r and
// p or (q or r), with p = strong(a), q = strong(b ##1 b) and r = strong(c), are
// neutrally satisfied by the same words, which are those opening with a, with
// b b, or with c.
TEST(DerivedFormConventions, PropertyOrGroupsEitherWay) {
  auto p = PropStrong(BoolSeq("a"));
  auto q = PropStrong(SeqConcat(BoolSeq("b"), BoolSeq("b")));
  auto r = PropStrong(BoolSeq("c"));
  auto left = PropOr(PropOr(p, q), r);
  auto right = PropOr(p, PropOr(q, r));
  std::size_t matches = 0;
  for (const auto& word : WordsUpTo(UnclockedAlphabet(), 3)) {
    bool holds = NeutrallySatisfies(word, *left);
    EXPECT_EQ(holds, NeutrallySatisfies(word, *right));
    if (holds) ++matches;
  }
  // 21 words open with a, 21 with c, and 5 with b b.
  EXPECT_EQ(matches, 47u);
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"b"}), A({"b"})}, *left));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"c"}), A({"b"})}, *right));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"b"}), A({"a"})}, *left));
  EXPECT_FALSE(NeutrallySatisfies(Word{}, *right));
}

}  // namespace
