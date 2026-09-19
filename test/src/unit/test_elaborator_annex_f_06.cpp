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

// §F.6 opens by fixing what the extended expressions of §F.6.1 through
// §F.6.3 share: a meaning at a point of a word that may depend on the letter
// there and on other letters, written e[w^j] so that the definitions of the
// preceding subclauses, which read a Boolean at a letter alone, can be used
// together with them. The cases check that a Boolean atom read as an extended
// expression depends on its letter alone while $past_gclk and $future_gclk
// depend on the letter before and after, that reading an extended expression
// into a word sets its atom at exactly the points it holds and leaves the
// undefined points and the letters T and _|_ alone, and that the word so read
// is one the relations of §F.5 decide as they decide any word.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto Bs(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// §F.6: a Boolean atom is the extended expression that reads its letter
// alone, T satisfying it and _|_ not, and undefined past the word; $past_gclk
// of it reads the letter before, with the initial value at the first letter;
// $future_gclk of it reads the letter after, and is undefined at the last
// letter of a finite word.
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

// §F.6: the meaning of an extended expression at a point may depend on other
// letters, which a Boolean's does not. At the second letter of [x][x],
// $past_gclk(a) differs from its value on [a][x], whose second letter is the
// same, and $future_gclk(a) from its value on [x][x][a], while the atom a
// itself agrees on every word carrying x there; a word that differs at the
// point shows nothing.
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

// §F.6: reading an extended expression into a word sets its atom at exactly
// the points at which it holds and clears it where it does not, leaves a
// point at which it is undefined as it stands, and keeps the letters T and
// _|_, which satisfy every Boolean and none.
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

// §F.6: the word so read is decided by the preceding subclauses as any word
// is. strong( a ##1 p ) with p read as $past_gclk(a) holds on [a][x], whose
// second letter takes p from the first, and not on [x][x]; with p read as
// $future_gclk(a) it holds on [a][x][a] and not on [a][x][x]; and the same
// property on the word as written, where p is an atom of its own, holds on
// neither.
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
