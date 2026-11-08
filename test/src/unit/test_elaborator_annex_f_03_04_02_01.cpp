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

Word Repeated(const Letter& letter, unsigned int count) {
  return Word(count, letter);
}

TEST(DerivedConsecutiveRepetition, ExactCountUnfoldsToConcatenations) {
  auto a = BoolSeq("a");
  EXPECT_TRUE(SequenceExprEqual(*SeqRepeatExactly(a, 0), *SeqNullRepeat(a)));
  EXPECT_TRUE(SequenceExprEqual(*SeqRepeatExactly(a, 2),
                                *SeqConcat(SeqConcat(SeqNullRepeat(a), a), a)));

  auto twice = SeqRepeatExactly(a, 2);
  EXPECT_TRUE(TightlySatisfies(Repeated(A({"a"}), 2), *twice));
  EXPECT_FALSE(TightlySatisfies(Repeated(A({"a"}), 1), *twice));
  EXPECT_FALSE(TightlySatisfies(Repeated(A({"a"}), 3), *twice));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"b"})}, *twice));
  EXPECT_TRUE(TightlySatisfies(Word{}, *SeqRepeatExactly(a, 0)));
  EXPECT_FALSE(TightlySatisfies(Word{}, *twice));

  auto pair_twice = SeqRepeatExactly(SeqConcat(a, BoolSeq("b")), 2);
  EXPECT_TRUE(TightlySatisfies(Word{A({"a"}), A({"b"}), A({"a"}), A({"b"})},
                               *pair_twice));
  EXPECT_FALSE(
      TightlySatisfies(Word{A({"a"}), A({"b"}), A({"a"})}, *pair_twice));
}

TEST(DerivedConsecutiveRepetition, RangeUnfoldsToAlternativesOfExactCounts) {
  auto a = BoolSeq("a");
  EXPECT_TRUE(
      SequenceExprEqual(*SeqRepeatRange(a, 2, 2), *SeqRepeatExactly(a, 2)));
  EXPECT_TRUE(SequenceExprEqual(
      *SeqRepeatRange(a, 1, 3),
      *SeqOr(SeqOr(SeqRepeatExactly(a, 1), SeqRepeatExactly(a, 2)),
             SeqRepeatExactly(a, 3))));

  auto one_to_three = SeqRepeatRange(a, 1, 3);
  EXPECT_FALSE(TightlySatisfies(Repeated(A({"a"}), 0), *one_to_three));
  EXPECT_TRUE(TightlySatisfies(Repeated(A({"a"}), 1), *one_to_three));
  EXPECT_TRUE(TightlySatisfies(Repeated(A({"a"}), 2), *one_to_three));
  EXPECT_TRUE(TightlySatisfies(Repeated(A({"a"}), 3), *one_to_three));
  EXPECT_FALSE(TightlySatisfies(Repeated(A({"a"}), 4), *one_to_three));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"b"})}, *one_to_three));
}

TEST(DerivedConsecutiveRepetition, UnboundedRangeUnfoldsToAPrefixAndATail) {
  auto a = BoolSeq("a");
  EXPECT_TRUE(
      SequenceExprEqual(*SeqRepeatAtLeast(a, 0),
                        *SeqOr(SeqNullRepeat(a), SeqUnboundedRepeat(a))));
  EXPECT_TRUE(
      SequenceExprEqual(*SeqRepeatAtLeast(a, 1), *SeqUnboundedRepeat(a)));
  EXPECT_TRUE(SequenceExprEqual(
      *SeqRepeatAtLeast(a, 2),
      *SeqConcat(SeqRepeatExactly(a, 1), SeqUnboundedRepeat(a))));

  auto two_or_more = SeqRepeatAtLeast(a, 2);
  EXPECT_FALSE(TightlySatisfies(Repeated(A({"a"}), 0), *two_or_more));
  EXPECT_FALSE(TightlySatisfies(Repeated(A({"a"}), 1), *two_or_more));
  EXPECT_TRUE(TightlySatisfies(Repeated(A({"a"}), 2), *two_or_more));
  EXPECT_TRUE(TightlySatisfies(Repeated(A({"a"}), 5), *two_or_more));
  EXPECT_FALSE(
      TightlySatisfies(Word{A({"a"}), A({"b"}), A({"a"})}, *two_or_more));
  EXPECT_TRUE(TightlySatisfies(Word{}, *SeqRepeatAtLeast(a, 0)));
}

TEST(DerivedConsecutiveRepetition, StarAndPlusUnfoldToTheTwoPrimitives) {
  auto a = BoolSeq("a");
  EXPECT_TRUE(
      SequenceExprEqual(*SeqRepeatZeroOrMore(a),
                        *SeqOr(SeqNullRepeat(a), SeqUnboundedRepeat(a))));
  EXPECT_TRUE(
      SequenceExprEqual(*SeqRepeatOneOrMore(a), *SeqUnboundedRepeat(a)));

  auto star = SeqRepeatZeroOrMore(a);
  auto plus = SeqRepeatOneOrMore(a);
  EXPECT_TRUE(TightlySatisfies(Word{}, *star));
  EXPECT_FALSE(TightlySatisfies(Word{}, *plus));
  EXPECT_TRUE(TightlySatisfies(Repeated(A({"a"}), 1), *star));
  EXPECT_TRUE(TightlySatisfies(Repeated(A({"a"}), 1), *plus));
  EXPECT_TRUE(TightlySatisfies(Repeated(A({"a"}), 3), *star));
  EXPECT_TRUE(TightlySatisfies(Repeated(A({"a"}), 3), *plus));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"b"})}, *star));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"b"})}, *plus));
}

}  // namespace
