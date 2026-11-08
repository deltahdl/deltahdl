#include <gtest/gtest.h>

#include <cstddef>
#include <optional>
#include <set>
#include <string>
#include <utility>

#include "elaborator/annex_f_extended_expressions.h"
#include "elaborator/annex_f_future.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

TEST(FutureGclk, SamplesTheFollowingLetter) {
  const Word kWord{A({}), A({}), A({})};
  EXPECT_EQ(FutureGclkSourceIndex(kWord, 0), std::optional<std::size_t>{1});
  EXPECT_EQ(FutureGclkSourceIndex(kWord, 1), std::optional<std::size_t>{2});
}

TEST(FutureGclk, UndefinedAtTheLastLetterOfAFiniteWord) {
  const Word kWord{A({}), A({}), A({})};
  EXPECT_EQ(FutureGclkSourceIndex(kWord, 2), std::nullopt);
  EXPECT_TRUE(FutureGclkIsUndefined(kWord, 2));
  EXPECT_FALSE(FutureGclkIsUndefined(kWord, 1));
}

TEST(FutureGclk, RejectsOutOfRangePoint) {
  const Word kWord{A({}), A({})};
  EXPECT_EQ(FutureGclkSourceIndex(kWord, 2), std::nullopt);
  EXPECT_FALSE(FutureGclkIsUndefined(kWord, 2));
}

TEST(FutureGclk, RejectsEmptyWord) {
  const Word kWord{};
  EXPECT_EQ(FutureGclkSourceIndex(kWord, 0), std::nullopt);
  EXPECT_FALSE(FutureGclkIsUndefined(kWord, 0));
}

TEST(FutureGclk, SingleLetterWordIsUndefinedAtItsOnlyPoint) {
  const Word kWord{A({"en"})};
  EXPECT_EQ(FutureGclkSourceIndex(kWord, 0), std::nullopt);
  EXPECT_TRUE(FutureGclkIsUndefined(kWord, 0));
}

TEST(FutureGclk, TheExpressionReadsTheFollowingLetterAndIsUndefinedAtTheLast) {
  auto future = FutureGclkOfAtom("a");
  const Word kWord{A({"x"}), A({"a"}), A({"x"})};
  EXPECT_EQ(future(kWord, 0), true);
  EXPECT_EQ(future(kWord, 1), false);
  EXPECT_EQ(future(kWord, 2), std::nullopt);
  EXPECT_EQ(future(kWord, 3), std::nullopt);
  auto p = PropStrong(
      SeqConcat(SeqBoolean(BoolAtom("p")), SeqBoolean(BoolAtom("a"))));
  EXPECT_TRUE(NeutrallySatisfies(
      WordWithExtendedAtom(Word{A({"x"}), A({"a"})}, "p", future), *p));
  EXPECT_FALSE(NeutrallySatisfies(
      WordWithExtendedAtom(Word{A({"a"}), A({"x"})}, "p", future), *p));
}

TEST(FutureGclk, OnAnInfiniteWordTheLastLetterOfThePrefixReadsTheTail) {
  const Word kWord{A({"x"}), A({"a"}), A({"x"})};
  auto top = FutureGclkOfAtomOnCompletion("a", LetterTop());
  auto bottom = FutureGclkOfAtomOnCompletion("a", LetterBottom());
  EXPECT_EQ(top(kWord, 2), true);
  EXPECT_EQ(bottom(kWord, 2), false);
  EXPECT_EQ(top(kWord, 3), true);
  EXPECT_EQ(bottom(kWord, 3), false);
  for (std::size_t j = 0; j < 2; ++j) {
    EXPECT_EQ(top(kWord, j), FutureGclkOfAtom("a")(kWord, j));
    EXPECT_EQ(bottom(kWord, j), FutureGclkOfAtom("a")(kWord, j));
  }
  EXPECT_EQ(top(Word{A({"x"})}, 0), true);
  EXPECT_EQ(FutureGclkOfAtom("a")(Word{A({"x"})}, 0), std::nullopt);
}

}  // namespace
