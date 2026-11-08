#include <gtest/gtest.h>

#include <set>
#include <string>
#include <utility>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_word_ops_internal.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

TEST(SemanticAlphabet, EveryLetterIsAtomSetTopOrBottom) {
  EXPECT_EQ(LetterTop().kind, Letter::Kind::kTop);
  EXPECT_EQ(LetterBottom().kind, Letter::Kind::kBottom);

  EXPECT_EQ(A({}).kind, Letter::Kind::kAtomSet);
  EXPECT_TRUE(A({}).atoms.empty());
  EXPECT_EQ(A({"a"}).kind, Letter::Kind::kAtomSet);
  EXPECT_EQ(A({"a", "b"}).atoms, (std::set<std::string>{"a", "b"}));

  EXPECT_NE(LetterTop().kind, LetterBottom().kind);
  EXPECT_NE(LetterTop().kind, A({"a"}).kind);
}

TEST(LetterBooleanSatisfaction, TopLetterSatisfiesEveryBoolean) {
  auto contradiction = BoolAnd(BoolAtom("a"), BoolNot(BoolAtom("a")));
  EXPECT_TRUE(LetterSatisfiesBoolean(LetterTop(), *BoolTrue()));
  EXPECT_TRUE(LetterSatisfiesBoolean(LetterTop(), *BoolAtom("a")));
  EXPECT_TRUE(LetterSatisfiesBoolean(LetterTop(), *BoolNot(BoolAtom("a"))));
  EXPECT_TRUE(LetterSatisfiesBoolean(LetterTop(), *contradiction));
}

TEST(LetterBooleanSatisfaction, BottomLetterSatisfiesNoBoolean) {
  EXPECT_FALSE(LetterSatisfiesBoolean(LetterBottom(), *BoolTrue()));
  EXPECT_FALSE(LetterSatisfiesBoolean(LetterBottom(), *BoolAtom("a")));
  EXPECT_FALSE(LetterSatisfiesBoolean(LetterBottom(), *BoolNot(BoolAtom("a"))));
}

TEST(LetterBooleanSatisfaction, AtomSetLetterEvaluatesPropositions) {
  Letter letter = A({"a"});
  EXPECT_TRUE(LetterSatisfiesBoolean(letter, *BoolTrue()));
  EXPECT_TRUE(LetterSatisfiesBoolean(letter, *BoolAtom("a")));
  EXPECT_FALSE(LetterSatisfiesBoolean(letter, *BoolAtom("b")));
  EXPECT_TRUE(LetterSatisfiesBoolean(letter, *BoolNot(BoolAtom("b"))));
  EXPECT_FALSE(
      LetterSatisfiesBoolean(letter, *BoolAnd(BoolAtom("a"), BoolAtom("b"))));
  EXPECT_TRUE(LetterSatisfiesBoolean(A({"a", "b"}),
                                     *BoolAnd(BoolAtom("a"), BoolAtom("b"))));
}

TEST(WordComplement, LetterComplementSwapsTopAndBottomKeepsAtomSet) {
  EXPECT_EQ(ComplementLetter(LetterTop()).kind, Letter::Kind::kBottom);
  EXPECT_EQ(ComplementLetter(LetterBottom()).kind, Letter::Kind::kTop);

  Letter atom = A({"a", "b"});
  Letter complemented = ComplementLetter(atom);
  EXPECT_EQ(complemented.kind, Letter::Kind::kAtomSet);
  EXPECT_EQ(complemented.atoms, atom.atoms);

  EXPECT_FALSE(
      LetterSatisfiesBoolean(ComplementLetter(LetterTop()), *BoolTrue()));
  EXPECT_TRUE(
      LetterSatisfiesBoolean(ComplementLetter(LetterBottom()), *BoolTrue()));
}

TEST(WordComplement, WordComplementIsLetterwise) {
  Word word = {LetterTop(), LetterBottom(), A({"a"})};
  Word complemented = ComplementWord(word);
  ASSERT_EQ(complemented.size(), word.size());
  EXPECT_EQ(complemented[0].kind, Letter::Kind::kBottom);
  EXPECT_EQ(complemented[1].kind, Letter::Kind::kTop);
  EXPECT_EQ(complemented[2].kind, Letter::Kind::kAtomSet);
  EXPECT_EQ(complemented[2].atoms, (std::set<std::string>{"a"}));

  EXPECT_TRUE(ComplementWord(Word{}).empty());
}

TEST(WordSuffix, DeletesFirstILettersEmptyPastEnd) {
  Word word = {A({"a"}), A({"b"}), A({"c"})};

  EXPECT_EQ(Suffix(word, 0).size(), 3u);
  EXPECT_EQ(Suffix(word, 0)[0].atoms, (std::set<std::string>{"a"}));

  Word tail = Suffix(word, 1);
  ASSERT_EQ(tail.size(), 2u);
  EXPECT_EQ(tail[0].atoms, (std::set<std::string>{"b"}));
  EXPECT_EQ(tail[1].atoms, (std::set<std::string>{"c"}));

  EXPECT_TRUE(Suffix(word, 3).empty());
  EXPECT_TRUE(Suffix(word, 9).empty());
}

TEST(WordSubword, InclusivePrefixKeepsFirstKPlusOneLetters) {
  Word word = {A({"a"}), A({"b"}), A({"c"})};

  Word first = PrefixInclusive(word, 0);
  ASSERT_EQ(first.size(), 1u);
  EXPECT_EQ(first[0].atoms, (std::set<std::string>{"a"}));

  Word two = PrefixInclusive(word, 1);
  ASSERT_EQ(two.size(), 2u);
  EXPECT_EQ(two[1].atoms, (std::set<std::string>{"b"}));

  EXPECT_EQ(PrefixInclusive(word, 2).size(), 3u);
  EXPECT_EQ(PrefixInclusive(word, 9).size(), 3u);
}

}  // namespace
