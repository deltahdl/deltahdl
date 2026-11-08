#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto BoolSeq(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

auto One() { return SeqBoolean(BoolTrue()); }

Word BlanksThenA(unsigned int blanks) {
  Word word(blanks, A({}));
  word.push_back(A({"a"}));
  return word;
}

Word AGapB(unsigned int blanks) {
  Word word{A({"a"})};
  for (unsigned int i = 0; i < blanks; ++i) word.push_back(A({}));
  word.push_back(A({"b"}));
  return word;
}

TEST(DerivedDelay, UnaryDelayPutsARepetitionOfOneBeforeTheSequence) {
  auto a = BoolSeq("a");
  EXPECT_TRUE(SequenceExprEqual(*SeqDelayExactly(2, a),
                                *SeqConcat(SeqRepeatExactly(One(), 2), a)));
  EXPECT_TRUE(SequenceExprEqual(*SeqDelayRange(1, 2, a),
                                *SeqConcat(SeqRepeatRange(One(), 1, 2), a)));
  EXPECT_TRUE(SequenceExprEqual(*SeqDelayAtLeast(1, a),
                                *SeqConcat(SeqRepeatAtLeast(One(), 1), a)));

  auto two = SeqDelayExactly(2, a);
  EXPECT_TRUE(TightlySatisfies(BlanksThenA(2), *two));
  EXPECT_TRUE(TightlySatisfies(Word{A({"b"}), A({"a"}), A({"a"})}, *two));
  EXPECT_FALSE(TightlySatisfies(BlanksThenA(1), *two));
  EXPECT_FALSE(TightlySatisfies(BlanksThenA(3), *two));

  auto one_to_two = SeqDelayRange(1, 2, a);
  EXPECT_FALSE(TightlySatisfies(BlanksThenA(0), *one_to_two));
  EXPECT_TRUE(TightlySatisfies(BlanksThenA(1), *one_to_two));
  EXPECT_TRUE(TightlySatisfies(BlanksThenA(2), *one_to_two));
  EXPECT_FALSE(TightlySatisfies(BlanksThenA(3), *one_to_two));

  auto one_or_more = SeqDelayAtLeast(1, a);
  EXPECT_FALSE(TightlySatisfies(BlanksThenA(0), *one_or_more));
  EXPECT_TRUE(TightlySatisfies(BlanksThenA(1), *one_or_more));
  EXPECT_TRUE(TightlySatisfies(BlanksThenA(4), *one_or_more));
}

TEST(DerivedDelay, StarAndPlusDelaysAreTheUnboundedRanges) {
  auto a = BoolSeq("a");
  EXPECT_TRUE(
      SequenceExprEqual(*SeqDelayZeroOrMore(a), *SeqDelayAtLeast(0, a)));
  EXPECT_TRUE(SequenceExprEqual(*SeqDelayOneOrMore(a), *SeqDelayAtLeast(1, a)));

  auto star = SeqDelayZeroOrMore(a);
  auto plus = SeqDelayOneOrMore(a);
  EXPECT_TRUE(TightlySatisfies(BlanksThenA(0), *star));
  EXPECT_FALSE(TightlySatisfies(BlanksThenA(0), *plus));
  EXPECT_TRUE(TightlySatisfies(BlanksThenA(3), *star));
  EXPECT_TRUE(TightlySatisfies(BlanksThenA(3), *plus));
  EXPECT_FALSE(TightlySatisfies(Word{}, *star));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({})}, *plus));
}

TEST(DerivedDelay, PositiveBinaryDelayPutsOneTickFewerBetweenTheOperands) {
  auto a = BoolSeq("a");
  auto b = BoolSeq("b");
  EXPECT_TRUE(SequenceExprEqual(
      *SeqConcatDelayExactly(a, 3, b),
      *SeqConcat(SeqConcat(a, SeqRepeatExactly(One(), 2)), b)));
  EXPECT_TRUE(
      SequenceExprEqual(*SeqConcatDelayExactly(a, 1, b), *SeqConcat(a, b)));
  EXPECT_TRUE(SequenceExprEqual(
      *SeqConcatDelayRange(a, 2, 3, b),
      *SeqConcat(SeqConcat(a, SeqRepeatRange(One(), 1, 2)), b)));
  EXPECT_TRUE(SequenceExprEqual(
      *SeqConcatDelayAtLeast(a, 1, b),
      *SeqConcat(SeqConcat(a, SeqRepeatAtLeast(One(), 0)), b)));

  auto three = SeqConcatDelayExactly(a, 3, b);
  EXPECT_TRUE(TightlySatisfies(AGapB(2), *three));
  EXPECT_FALSE(TightlySatisfies(AGapB(1), *three));
  EXPECT_FALSE(TightlySatisfies(AGapB(3), *three));

  auto two_to_three = SeqConcatDelayRange(a, 2, 3, b);
  EXPECT_FALSE(TightlySatisfies(AGapB(0), *two_to_three));
  EXPECT_TRUE(TightlySatisfies(AGapB(1), *two_to_three));
  EXPECT_TRUE(TightlySatisfies(AGapB(2), *two_to_three));
  EXPECT_FALSE(TightlySatisfies(AGapB(3), *two_to_three));

  auto one_or_more = SeqConcatDelayAtLeast(a, 1, b);
  EXPECT_FALSE(TightlySatisfies(Word{A({"a", "b"})}, *one_or_more));
  EXPECT_TRUE(TightlySatisfies(AGapB(0), *one_or_more));
  EXPECT_TRUE(TightlySatisfies(AGapB(3), *one_or_more));
}

TEST(DerivedDelay, ZeroDelayIsTheFusionOrTheDelayFromOne) {
  auto a = BoolSeq("a");
  auto b = BoolSeq("b");
  EXPECT_TRUE(
      SequenceExprEqual(*SeqConcatDelayRange(a, 0, 0, b), *SeqFusion(a, b)));
  EXPECT_TRUE(
      SequenceExprEqual(*SeqConcatDelayExactly(a, 0, b), *SeqFusion(a, b)));
  EXPECT_TRUE(SequenceExprEqual(
      *SeqConcatDelayRange(a, 0, 2, b),
      *SeqOr(SeqFusion(a, b), SeqConcatDelayRange(a, 1, 2, b))));
  EXPECT_TRUE(SequenceExprEqual(
      *SeqConcatDelayAtLeast(a, 0, b),
      *SeqOr(SeqFusion(a, b), SeqConcatDelayAtLeast(a, 1, b))));

  auto zero = SeqConcatDelayRange(a, 0, 0, b);
  EXPECT_TRUE(TightlySatisfies(Word{A({"a", "b"})}, *zero));
  EXPECT_FALSE(TightlySatisfies(AGapB(0), *zero));

  auto zero_to_two = SeqConcatDelayRange(a, 0, 2, b);
  EXPECT_TRUE(TightlySatisfies(Word{A({"a", "b"})}, *zero_to_two));
  EXPECT_TRUE(TightlySatisfies(AGapB(0), *zero_to_two));
  EXPECT_TRUE(TightlySatisfies(AGapB(1), *zero_to_two));
  EXPECT_FALSE(TightlySatisfies(AGapB(2), *zero_to_two));

  auto zero_or_more = SeqConcatDelayAtLeast(a, 0, b);
  EXPECT_TRUE(TightlySatisfies(Word{A({"a", "b"})}, *zero_or_more));
  EXPECT_TRUE(TightlySatisfies(AGapB(4), *zero_or_more));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"c"})}, *zero_or_more));
}

}  // namespace
