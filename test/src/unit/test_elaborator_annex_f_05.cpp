#include <gtest/gtest.h>

#include <set>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_word_ops_internal.h"

// §F.5 head: the formal-semantics foundation shared by every descendant
// (§F.5.1 rewrite rules through §F.5.6 satisfaction with local variables).
// Its own text fixes the alphabet Sigma = 2^P U {T, _|_}, the letter-level
// satisfaction base (T satisfies every Boolean, _|_ none), the word-bar
// complement, the suffix w^{i.}, and the finite subword w^{i,j}. These are
// pure operations over semantic words -- values that no SystemVerilog source
// text produces -- so each rule is observed directly at the elaborator stage
// on hand-built letters and words rather than through a descendant relation.

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// §F.5 head, alphabet Sigma = 2^P U {T, _|_}: a letter is exactly one of an
// element of 2^P, the top letter, or the bottom letter, and an atom-set letter
// records its propositions. The empty set, a singleton, and a multi-atom set
// are all legal elements of 2^P.
TEST(SemanticAlphabet, EveryLetterIsAtomSetTopOrBottom) {
  EXPECT_EQ(LetterTop().kind, Letter::Kind::kTop);
  EXPECT_EQ(LetterBottom().kind, Letter::Kind::kBottom);

  EXPECT_EQ(A({}).kind, Letter::Kind::kAtomSet);
  EXPECT_TRUE(A({}).atoms.empty());
  EXPECT_EQ(A({"a"}).kind, Letter::Kind::kAtomSet);
  EXPECT_EQ(A({"a", "b"}).atoms, (std::set<std::string>{"a", "b"}));

  // The three kinds are distinct: top is neither bottom nor an atom-set.
  EXPECT_NE(LetterTop().kind, LetterBottom().kind);
  EXPECT_NE(LetterTop().kind, A({"a"}).kind);
}

// §F.5 head, satisfaction base for the top letter: T |= b for every Boolean b,
// including a Boolean that no ordinary atom-set could satisfy (here a & !a).
TEST(LetterBooleanSatisfaction, TopLetterSatisfiesEveryBoolean) {
  auto contradiction = BoolAnd(BoolAtom("a"), BoolNot(BoolAtom("a")));
  EXPECT_TRUE(LetterSatisfiesBoolean(LetterTop(), *BoolTrue()));
  EXPECT_TRUE(LetterSatisfiesBoolean(LetterTop(), *BoolAtom("a")));
  EXPECT_TRUE(LetterSatisfiesBoolean(LetterTop(), *BoolNot(BoolAtom("a"))));
  EXPECT_TRUE(LetterSatisfiesBoolean(LetterTop(), *contradiction));
}

// §F.5 head, satisfaction base for the bottom letter: _|_ |/= b for every
// Boolean b, including the constantly-true Boolean -- the strongest negative,
// since even an unconditionally satisfied expression is rejected.
TEST(LetterBooleanSatisfaction, BottomLetterSatisfiesNoBoolean) {
  EXPECT_FALSE(LetterSatisfiesBoolean(LetterBottom(), *BoolTrue()));
  EXPECT_FALSE(LetterSatisfiesBoolean(LetterBottom(), *BoolAtom("a")));
  EXPECT_FALSE(LetterSatisfiesBoolean(LetterBottom(), *BoolNot(BoolAtom("a"))));
}

// §F.5 head, satisfaction base for a letter in 2^P: the Boolean is evaluated
// against the set of true propositions. An atom holds iff it is in the set;
// negation, conjunction, and the constant true compose from that, and an atom
// absent from the set is the negative case.
TEST(LetterBooleanSatisfaction, AtomSetLetterEvaluatesPropositions) {
  Letter letter = A({"a"});
  EXPECT_TRUE(LetterSatisfiesBoolean(letter, *BoolTrue()));
  EXPECT_TRUE(LetterSatisfiesBoolean(letter, *BoolAtom("a")));
  EXPECT_FALSE(LetterSatisfiesBoolean(letter, *BoolAtom("b")));
  EXPECT_TRUE(LetterSatisfiesBoolean(letter, *BoolNot(BoolAtom("b"))));
  // a & b needs both propositions; only "a" is present.
  EXPECT_FALSE(
      LetterSatisfiesBoolean(letter, *BoolAnd(BoolAtom("a"), BoolAtom("b"))));
  EXPECT_TRUE(LetterSatisfiesBoolean(A({"a", "b"}),
                                     *BoolAnd(BoolAtom("a"), BoolAtom("b"))));
}

// §F.5 head, complement w-bar interchanges T and _|_ and leaves a 2^P letter
// unchanged. The complement of the top letter satisfies no Boolean and the
// complement of the bottom letter satisfies every Boolean, tying the swap back
// to the satisfaction base.
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

// §F.5 head, complement extends letterwise to a whole word, and the complement
// of the empty word is empty.
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

// §F.5 head, suffix w^{i.} deletes the first i letters. Deleting none returns
// the whole word, deleting some returns the tail w^i w^{i+1}..., and deleting
// at least |w| letters yields the empty word -- the boundary the head states
// for i >= |w|.
TEST(WordSuffix, DeletesFirstILettersEmptyPastEnd) {
  Word word = {A({"a"}), A({"b"}), A({"c"})};

  EXPECT_EQ(Suffix(word, 0).size(), 3u);  // i = 0: whole word
  EXPECT_EQ(Suffix(word, 0)[0].atoms, (std::set<std::string>{"a"}));

  Word tail = Suffix(word, 1);  // 0 < i < |w|: proper tail
  ASSERT_EQ(tail.size(), 2u);
  EXPECT_EQ(tail[0].atoms, (std::set<std::string>{"b"}));
  EXPECT_EQ(tail[1].atoms, (std::set<std::string>{"c"}));

  EXPECT_TRUE(Suffix(word, 3).empty());  // i = |w|: empty
  EXPECT_TRUE(Suffix(word, 9).empty());  // i > |w|: still empty
}

// §F.5 head, finite subword w^{i,j} in its i = 0 form w^{0,k}: the finite
// prefix w^0 w^1 ... w^k. k = 0 keeps the first letter, an interior k keeps the
// first k+1 letters, and a k at or beyond the last index keeps the whole word.
TEST(WordSubword, InclusivePrefixKeepsFirstKPlusOneLetters) {
  Word word = {A({"a"}), A({"b"}), A({"c"})};

  Word first = PrefixInclusive(word, 0);  // w^{0,0}
  ASSERT_EQ(first.size(), 1u);
  EXPECT_EQ(first[0].atoms, (std::set<std::string>{"a"}));

  Word two = PrefixInclusive(word, 1);  // w^{0,1}
  ASSERT_EQ(two.size(), 2u);
  EXPECT_EQ(two[1].atoms, (std::set<std::string>{"b"}));

  EXPECT_EQ(PrefixInclusive(word, 2).size(), 3u);  // k at last index
  EXPECT_EQ(PrefixInclusive(word, 9).size(), 3u);  // k past end: clamped
}

}  // namespace
