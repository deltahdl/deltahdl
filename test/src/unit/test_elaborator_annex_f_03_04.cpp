#include <gtest/gtest.h>

#include <cstddef>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_sequence_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto BoolSeq(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

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
  EXPECT_EQ(matches, 47u);
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"b"}), A({"b"})}, *left));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"c"}), A({"b"})}, *right));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"b"}), A({"a"})}, *left));
  EXPECT_FALSE(NeutrallySatisfies(Word{}, *right));
}

}  // namespace
