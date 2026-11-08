#include <gtest/gtest.h>

#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_extended_expressions.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

TEST(ExtendedExpressions, EachKindReadsItsOwnLetters) {
  const Word kWord{A({"x"}), A({"a"}), LetterTop(), LetterBottom()};
  auto atom = AtomAsExtendedExpression("a");
  EXPECT_EQ(atom(kWord, 0), false);
  EXPECT_EQ(atom(kWord, 1), true);
  EXPECT_EQ(atom(kWord, 2), true);
  EXPECT_EQ(atom(kWord, 3), false);
  EXPECT_EQ(atom(kWord, 4), std::nullopt);
  auto past = PastGclkOfAtom("a", true);
  EXPECT_EQ(past(kWord, 0), true);
  EXPECT_EQ(PastGclkOfAtom("a", false)(kWord, 0), false);
  EXPECT_EQ(past(kWord, 1), false);
  EXPECT_EQ(past(kWord, 2), true);
  EXPECT_EQ(past(kWord, 3), true);
  EXPECT_EQ(past(kWord, 4), std::nullopt);
  auto future = FutureGclkOfAtom("a");
  EXPECT_EQ(future(kWord, 0), true);
  EXPECT_EQ(future(kWord, 1), true);
  EXPECT_EQ(future(kWord, 2), false);
  EXPECT_EQ(future(kWord, 3), std::nullopt);
}

TEST(ExtendedExpressions, OnlyAnExtendedExpressionDependsOnOtherLetters) {
  const Word kWord{A({"x"}), A({"x"})};
  const std::vector<Word> kOthers{Word{A({"a"}), A({"x"})},
                                  Word{A({"x"}), A({"x"}), A({"a"})},
                                  Word{A({"x"}), A({"a"})}};
  EXPECT_FALSE(
      DependsOnOtherLetters(AtomAsExtendedExpression("a"), kWord, 1, kOthers));
  EXPECT_TRUE(
      DependsOnOtherLetters(PastGclkOfAtom("a", false), kWord, 1, kOthers));
  EXPECT_TRUE(DependsOnOtherLetters(FutureGclkOfAtom("a"), kWord, 1, kOthers));
  EXPECT_FALSE(DependsOnOtherLetters(PastGclkOfAtom("a", false), kWord, 1,
                                     {Word{A({"x"}), A({"a"})}}));
  EXPECT_FALSE(DependsOnOtherLetters(PastGclkOfAtom("a", false), kWord, 1,
                                     {Word{A({"x"}), A({"x"})}}));
  EXPECT_FALSE(
      DependsOnOtherLetters(PastGclkOfAtom("a", false), kWord, 2, kOthers));
}

TEST(ExtendedExpressions, ReadingIntoTheWordSetsTheAtomWhereItHolds) {
  const Word kWord{A({"a"}), A({"x", "p"}),  A({"a", "p"}), LetterTop(),
                   A({"x"}), LetterBottom(), A({"p"})};
  const Word kPast =
      WordWithExtendedAtom(kWord, "p", PastGclkOfAtom("a", false));
  ASSERT_EQ(kPast.size(), kWord.size());
  EXPECT_EQ(kPast[0].atoms, std::set<std::string>({"a"}));
  EXPECT_EQ(kPast[1].atoms, std::set<std::string>({"x", "p"}));
  EXPECT_EQ(kPast[2].atoms, std::set<std::string>({"a"}));
  EXPECT_EQ(kPast[3].kind, Letter::Kind::kTop);
  EXPECT_EQ(kPast[4].atoms, std::set<std::string>({"x", "p"}));
  EXPECT_EQ(kPast[5].kind, Letter::Kind::kBottom);
  EXPECT_EQ(kPast[6].atoms, std::set<std::string>());
  const Word kFuture = WordWithExtendedAtom(kWord, "p", FutureGclkOfAtom("a"));
  EXPECT_EQ(kFuture[0].atoms, std::set<std::string>({"a"}));
  EXPECT_EQ(kFuture[1].atoms, std::set<std::string>({"x", "p"}));
  EXPECT_EQ(kFuture[2].atoms, std::set<std::string>({"a", "p"}));
  EXPECT_EQ(kFuture[4].atoms, std::set<std::string>({"x"}));
  EXPECT_EQ(kFuture[6].atoms, std::set<std::string>({"p"}));
  EXPECT_TRUE(WordWithExtendedAtom(Word{}, "p", FutureGclkOfAtom("a")).empty());
}

TEST(ExtendedExpressions, TheWordReadIsDecidedByThePrecedingSubclauses) {
  auto p = PropStrong(SeqConcat(Bs("a"), Bs("p")));
  auto past = PastGclkOfAtom("a", false);
  auto future = FutureGclkOfAtom("a");
  const Word kAX{A({"a"}), A({"x"})};
  const Word kXX{A({"x"}), A({"x"})};
  const Word kAXA{A({"a"}), A({"x"}), A({"a"})};
  const Word kAXX{A({"a"}), A({"x"}), A({"x"})};
  EXPECT_TRUE(NeutrallySatisfies(WordWithExtendedAtom(kAX, "p", past), *p));
  EXPECT_FALSE(NeutrallySatisfies(WordWithExtendedAtom(kXX, "p", past), *p));
  EXPECT_TRUE(NeutrallySatisfies(WordWithExtendedAtom(kAXA, "p", future), *p));
  EXPECT_FALSE(NeutrallySatisfies(WordWithExtendedAtom(kAXX, "p", future), *p));
  EXPECT_FALSE(NeutrallySatisfies(kAX, *p));
  EXPECT_FALSE(NeutrallySatisfies(kAXA, *p));
}

}  // namespace
