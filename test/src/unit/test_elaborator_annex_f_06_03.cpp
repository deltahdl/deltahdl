#include <gtest/gtest.h>

#include <cstddef>
#include <optional>
#include <set>
#include <string>
#include <utility>

#include "elaborator/annex_f_future.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

// A single alphabet letter carrying the given atomic propositions.
Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// §F.6.3: $future_gclk(e)[w^j] = e[w^{j+1}], so the source is the immediately
// following letter.
TEST(FutureGclk, SamplesTheFollowingLetter) {
  const Word word{A({}), A({}), A({})};
  EXPECT_EQ(FutureGclkSourceIndex(word, /*j=*/0), std::optional<std::size_t>{1});
  EXPECT_EQ(FutureGclkSourceIndex(word, /*j=*/1), std::optional<std::size_t>{2});
}

// §F.6.3: for a finite word the value at the last letter, j == |w| - 1, is
// undefined -- there is no following letter -- so no source index is reported.
TEST(FutureGclk, UndefinedAtTheLastLetterOfAFiniteWord) {
  const Word word{A({}), A({}), A({})};
  EXPECT_EQ(FutureGclkSourceIndex(word, /*j=*/2), std::nullopt);
  EXPECT_TRUE(FutureGclkIsUndefined(word, /*j=*/2));
  // A point with a following letter is defined, not the undefined last letter.
  EXPECT_FALSE(FutureGclkIsUndefined(word, /*j=*/1));
}

// §F.6.3 boundary: a point past the end of the word lies outside the rule's
// domain (0 <= j < |w| - 1), yields no source index, and is not the named
// "undefined" last letter.
TEST(FutureGclk, RejectsOutOfRangePoint) {
  const Word word{A({}), A({})};
  EXPECT_EQ(FutureGclkSourceIndex(word, /*j=*/2), std::nullopt);
  EXPECT_FALSE(FutureGclkIsUndefined(word, /*j=*/2));
}

// §F.6.3 requires a nonempty word; an empty word has no defined point at all.
TEST(FutureGclk, RejectsEmptyWord) {
  const Word word{};
  EXPECT_EQ(FutureGclkSourceIndex(word, /*j=*/0), std::nullopt);
  EXPECT_FALSE(FutureGclkIsUndefined(word, /*j=*/0));
}

// §F.6.3: a single-letter finite word has only the last letter w^0, where the
// value is undefined; there is no point with a following letter.
TEST(FutureGclk, SingleLetterWordIsUndefinedAtItsOnlyPoint) {
  const Word word{A({"en"})};
  EXPECT_EQ(FutureGclkSourceIndex(word, /*j=*/0), std::nullopt);
  EXPECT_TRUE(FutureGclkIsUndefined(word, /*j=*/0));
}

}  // namespace
