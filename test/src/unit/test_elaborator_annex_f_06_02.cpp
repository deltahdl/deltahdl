#include <gtest/gtest.h>

#include <cstddef>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_extended_expressions.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_past.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto One() { return BoolTrue(); }

using Indices = std::vector<std::size_t>;

TEST(Past, DefaultFormSamplesThePrecedingLetter) {
  const Word kWord{A({}), A({}), A({})};
  EXPECT_EQ(PastSourceIndices(kWord, 2, 1, One(), One()), Indices{1});
  EXPECT_EQ(PastSourceIndices(kWord, 1, 1, One(), One()), Indices{0});
}

TEST(Past, NTicksBackWithEveryTickActive) {
  const Word kWord{A({}), A({}), A({}), A({})};
  EXPECT_EQ(PastSourceIndices(kWord, 3, 2, One(), One()), Indices{1});
  EXPECT_EQ(PastSourceIndices(kWord, 3, 3, One(), One()), Indices{0});
}

TEST(Past, GatingExpressionCountsOnlyActiveTicks) {
  auto en = BoolAtom("en");
  const Word kWord{A({"en"}), A({}), A({"en"}), A({})};
  EXPECT_EQ(PastSourceIndices(kWord, 3, 1, en, One()), Indices{2});
  EXPECT_EQ(PastSourceIndices(kWord, 3, 2, en, One()), Indices{0});
}

TEST(Past, ClockGatesTicks) {
  auto clk = BoolAtom("clk");
  const Word kWord{A({}), A({"clk"}), A({}), A({"clk"})};
  EXPECT_EQ(PastSourceIndices(kWord, 3, 1, One(), clk), Indices{1});
}

TEST(Past, ClockAndGateBothRequiredForATick) {
  auto clk = BoolAtom("clk");
  auto en = BoolAtom("en");
  const Word kWord{A({"clk", "en"}), A({"clk"}), A({"clk", "en"})};
  EXPECT_EQ(PastSourceIndices(kWord, 2, 1, en, clk), Indices{0});
}

TEST(Past, FallsBackToInitialValueWhenTooFewTicks) {
  auto en = BoolAtom("en");
  const Word kWord{A({"en"}), A({}), A({})};
  EXPECT_TRUE(PastSourceIndices(kWord, 2, 2, en, One()).empty());
  EXPECT_TRUE(PastSamplesInitialValue(kWord, 2, 2, en, One()));
  EXPECT_FALSE(PastSamplesInitialValue(kWord, 2, 1, en, One()));
}

TEST(Past, TakesInitialValueAtTheFirstLetter) {
  const Word kWord{A({"en"}), A({"en"})};
  auto en = BoolAtom("en");
  EXPECT_TRUE(PastSourceIndices(kWord, 0, 1, en, One()).empty());
  EXPECT_TRUE(PastSamplesInitialValue(kWord, 0, 1, en, One()));
}

TEST(Past, RejectsOutOfRangePoint) {
  const Word kWord{A({}), A({})};
  EXPECT_TRUE(PastSourceIndices(kWord, 2, 1, One(), One()).empty());
  EXPECT_FALSE(PastSamplesInitialValue(kWord, 2, 1, One(), One()));
}

TEST(Past, RejectsZeroTickCount) {
  const Word kWord{A({}), A({})};
  EXPECT_TRUE(PastSourceIndices(kWord, 1, 0, One(), One()).empty());
  EXPECT_FALSE(PastSamplesInitialValue(kWord, 1, 0, One(), One()));
}

TEST(PastGclk, SamplesThePrecedingLetter) {
  const Word kWord{A({}), A({}), A({})};
  EXPECT_EQ(PastGclkSourceIndex(kWord, 2), std::optional<std::size_t>{1});
  EXPECT_EQ(PastGclkSourceIndex(kWord, 1), std::optional<std::size_t>{0});
}

TEST(PastGclk, TakesInitialValueAtTheFirstLetter) {
  const Word kWord{A({}), A({})};
  EXPECT_EQ(PastGclkSourceIndex(kWord, 0), std::nullopt);
}

TEST(PastGclk, RejectsOutOfRangePoint) {
  const Word kWord{A({}), A({})};
  EXPECT_EQ(PastGclkSourceIndex(kWord, 2), std::nullopt);
}

TEST(Past, TheInitialValueFollowsTheDeclarationForAStaticVariable) {
  EXPECT_TRUE(PastInitialValue(VariableKind::kStatic, true, false));
  EXPECT_FALSE(PastInitialValue(VariableKind::kStatic, false, true));
  EXPECT_FALSE(PastInitialValue(VariableKind::kStatic, std::nullopt, false));
  EXPECT_TRUE(PastInitialValue(VariableKind::kStatic, std::nullopt, true));
  EXPECT_FALSE(PastInitialValue(VariableKind::kOther, true, false));
  EXPECT_TRUE(PastInitialValue(VariableKind::kOther, false, true));
}

TEST(Past, TheExpressionReadsTheSourceLetter) {
  auto en = BoolAtom("en");
  auto clk = BoolAtom("clk");
  const Word kWord{A({"a", "en", "clk"}), A({"x"}), A({"a", "en", "clk"}),
                   A({"x", "en"}), A({"x", "en", "clk"})};
  auto past = PastOfAtom("a", 2, en, clk, false);
  EXPECT_EQ(past(kWord, 4), true);
  EXPECT_EQ(past(kWord, 2), false);
  EXPECT_EQ(PastOfAtom("a", 2, en, clk, true)(kWord, 2), true);
  EXPECT_EQ(past(kWord, 5), std::nullopt);
  EXPECT_EQ(PastOfAtom("a", 0, en, clk, false)(kWord, 4), std::nullopt);
  for (std::size_t j = 0; j < kWord.size(); ++j) {
    const Indices kSources = PastSourceIndices(kWord, j, 2, en, clk);
    const std::optional<bool> kExpected =
        kSources.empty() ? std::optional<bool>{false}
                         : std::optional<bool>{LetterSatisfiesBoolean(
                               kWord[kSources.front()], *BoolAtom("a"))};
    EXPECT_EQ(past(kWord, j), kExpected);
  }
}

TEST(Past, TheDefaultFormIsTheFourArgumentOne) {
  const Word kWord{A({"a"}), A({"x"}), LetterTop(), LetterBottom(), A({"x"})};
  auto brief = PastOfAtom("a", true);
  auto full = PastOfAtom("a", 1, One(), One(), true);
  for (std::size_t j = 0; j <= kWord.size(); ++j) {
    EXPECT_EQ(brief(kWord, j), full(kWord, j));
  }
  EXPECT_EQ(brief(kWord, 0), true);
  EXPECT_EQ(brief(kWord, 1), true);
  EXPECT_EQ(brief(kWord, 2), false);
  EXPECT_EQ(brief(kWord, 3), true);
  EXPECT_EQ(brief(kWord, 4), true);
  EXPECT_EQ(PastOfAtom("a", false)(kWord, 3), false);
  EXPECT_EQ(PastOfAtom("a", false)(kWord, 4), false);
  EXPECT_EQ(brief(kWord, 5), std::nullopt);
}

TEST(Past, TheExpressionReadIntoAWordIsDecidedByThePrecedingSubclauses) {
  auto p =
      PropStrong(SeqConcat(SeqBoolean(BoolTrue()), SeqBoolean(BoolAtom("p"))));
  auto past = PastOfAtom("a", false);
  EXPECT_TRUE(NeutrallySatisfies(
      WordWithExtendedAtom(Word{A({"a"}), A({"x"})}, "p", past), *p));
  EXPECT_FALSE(NeutrallySatisfies(
      WordWithExtendedAtom(Word{A({"x"}), A({"a"})}, "p", past), *p));
}

}  // namespace
