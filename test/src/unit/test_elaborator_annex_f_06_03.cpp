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

// A single alphabet letter carrying the given atomic propositions.
Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// §F.6.3: $future_gclk(e)[w^j] = e[w^{j+1}], so the source is the immediately
// following letter.
TEST(FutureGclk, SamplesTheFollowingLetter) {
  const Word kWord{A({}), A({}), A({})};
  EXPECT_EQ(FutureGclkSourceIndex(kWord, /*j=*/0),
            std::optional<std::size_t>{1});
  EXPECT_EQ(FutureGclkSourceIndex(kWord, /*j=*/1),
            std::optional<std::size_t>{2});
}

// §F.6.3: for a finite word the value at the last letter, j == |w| - 1, is
// undefined -- there is no following letter -- so no source index is reported.
TEST(FutureGclk, UndefinedAtTheLastLetterOfAFiniteWord) {
  const Word kWord{A({}), A({}), A({})};
  EXPECT_EQ(FutureGclkSourceIndex(kWord, /*j=*/2), std::nullopt);
  EXPECT_TRUE(FutureGclkIsUndefined(kWord, /*j=*/2));
  // A point with a following letter is defined, not the undefined last letter.
  EXPECT_FALSE(FutureGclkIsUndefined(kWord, /*j=*/1));
}

// §F.6.3 boundary: a point past the end of the word lies outside the rule's
// domain (0 <= j < |w| - 1), yields no source index, and is not the named
// "undefined" last letter.
TEST(FutureGclk, RejectsOutOfRangePoint) {
  const Word kWord{A({}), A({})};
  EXPECT_EQ(FutureGclkSourceIndex(kWord, /*j=*/2), std::nullopt);
  EXPECT_FALSE(FutureGclkIsUndefined(kWord, /*j=*/2));
}

// §F.6.3 requires a nonempty word; an empty word has no defined point at all.
TEST(FutureGclk, RejectsEmptyWord) {
  const Word kWord{};
  EXPECT_EQ(FutureGclkSourceIndex(kWord, /*j=*/0), std::nullopt);
  EXPECT_FALSE(FutureGclkIsUndefined(kWord, /*j=*/0));
}

// §F.6.3: a single-letter finite word has only the last letter w^0, where the
// value is undefined; there is no point with a following letter.
TEST(FutureGclk, SingleLetterWordIsUndefinedAtItsOnlyPoint) {
  const Word kWord{A({"en"})};
  EXPECT_EQ(FutureGclkSourceIndex(kWord, /*j=*/0), std::nullopt);
  EXPECT_TRUE(FutureGclkIsUndefined(kWord, /*j=*/0));
}

// §F.6.3 under §F.6: $future_gclk(a) as an extended expression reads the
// following letter at every point but the last of a finite word, where it is
// undefined, and is undefined past the word; read into a word, it is decided
// by the preceding subclauses as any atom is, strong( p ##1 a ) with p read
// as $future_gclk(a) holding on [x][a] and not on [a][x].
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

// §F.6.3: the value is undefined at the last letter of a finite word alone.
// On the infinite word w T^omega every letter has a following one, so at the
// last letter of the prefix the expression reads T, which satisfies a, and
// on w _|_^omega it reads _|_, which does not; at the points before the last
// the completion changes nothing, and a point in the tail reads the tail.
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
