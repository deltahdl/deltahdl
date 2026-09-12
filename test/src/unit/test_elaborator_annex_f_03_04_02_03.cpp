#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

// §F.3.4.2.3 unfolds the nonconsecutive repetition operators of §16.9.2 over
// a Boolean b into consecutive repetitions of the unit (!b[*0:$] ##1 b), a
// run of letters without b ending at one with it: a goto repetition is that
// unit repeated, so the word ends at its last b, and a nonconsecutive
// repetition is the goto followed by one more run without b. Each case checks
// the tree a form unfolds to against the identity the subclause states, then
// the words that tightly satisfy it under §F.5.2.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// The letter without b, the letter with it.
Letter N() { return A({"a"}); }
Letter B() { return A({"b"}); }

// The unit (!b[*0:$] ##1 b) in the §F.3.4.2.1 unfolding of [*0:$].
std::shared_ptr<const SequenceExpr> Unit(
    const std::shared_ptr<const BooleanExpr>& b) {
  return SeqConcat(SeqRepeatAtLeast(SeqBoolean(BoolNot(b)), 0), SeqBoolean(b));
}

// b[->m] is (!b[*0:$] ##1 b)[*m]: a word with m letters b, ending at the
// last, whatever stands between.
TEST(DerivedNonconsecutiveRepetition, GotoCountsTheLettersAndEndsAtTheLast) {
  auto b = BoolAtom("b");
  EXPECT_TRUE(
      SequenceExprEqual(*SeqGotoExactly(b, 2), *SeqRepeatExactly(Unit(b), 2)));

  auto two = SeqGotoExactly(b, 2);
  EXPECT_TRUE(TightlySatisfies(Word{B(), B()}, *two));
  EXPECT_TRUE(TightlySatisfies(Word{N(), B(), N(), N(), B()}, *two));
  EXPECT_FALSE(TightlySatisfies(Word{B(), B(), N()}, *two));
  EXPECT_FALSE(TightlySatisfies(Word{B()}, *two));
  EXPECT_FALSE(TightlySatisfies(Word{B(), B(), B()}, *two));
  EXPECT_TRUE(TightlySatisfies(Word{}, *SeqGotoExactly(b, 0)));
}

// b[->m:n] is (!b[*0:$] ##1 b)[*m:n] and b[->m:$] is (!b[*0:$] ##1 b)[*m:$]:
// the count of letters b is bounded by the range, and the word still ends at
// the last of them.
TEST(DerivedNonconsecutiveRepetition, GotoRangesBoundTheCount) {
  auto b = BoolAtom("b");
  EXPECT_TRUE(SequenceExprEqual(*SeqGotoRange(b, 1, 2),
                                *SeqRepeatRange(Unit(b), 1, 2)));
  EXPECT_TRUE(
      SequenceExprEqual(*SeqGotoAtLeast(b, 2), *SeqRepeatAtLeast(Unit(b), 2)));

  auto one_to_two = SeqGotoRange(b, 1, 2);
  EXPECT_FALSE(TightlySatisfies(Word{N()}, *one_to_two));
  EXPECT_TRUE(TightlySatisfies(Word{N(), B()}, *one_to_two));
  EXPECT_TRUE(TightlySatisfies(Word{B(), N(), B()}, *one_to_two));
  EXPECT_FALSE(TightlySatisfies(Word{B(), B(), B()}, *one_to_two));
  EXPECT_FALSE(TightlySatisfies(Word{B(), N()}, *one_to_two));

  auto two_or_more = SeqGotoAtLeast(b, 2);
  EXPECT_FALSE(TightlySatisfies(Word{N(), B()}, *two_or_more));
  EXPECT_TRUE(TightlySatisfies(Word{B(), N(), B()}, *two_or_more));
  EXPECT_TRUE(TightlySatisfies(Word{B(), B(), N(), B(), B()}, *two_or_more));
  EXPECT_FALSE(TightlySatisfies(Word{B(), B(), N()}, *two_or_more));
}

// b[=m] is (b[->m] ##1 !b[*0:$]), and the ranges likewise end in a run
// without b: the count of letters b is what the form names, and the word may
// go on past the last of them through letters without b.
TEST(DerivedNonconsecutiveRepetition, NonconsecutiveAllowsARunAfterTheLast) {
  auto b = BoolAtom("b");
  auto run_without = SeqRepeatAtLeast(SeqBoolean(BoolNot(b)), 0);
  EXPECT_TRUE(SequenceExprEqual(*SeqNonconsecutiveExactly(b, 2),
                                *SeqConcat(SeqGotoExactly(b, 2), run_without)));
  EXPECT_TRUE(
      SequenceExprEqual(*SeqNonconsecutiveRange(b, 1, 2),
                        *SeqConcat(SeqGotoRange(b, 1, 2), run_without)));
  EXPECT_TRUE(SequenceExprEqual(*SeqNonconsecutiveAtLeast(b, 2),
                                *SeqConcat(SeqGotoAtLeast(b, 2), run_without)));

  auto two = SeqNonconsecutiveExactly(b, 2);
  EXPECT_TRUE(TightlySatisfies(Word{B(), B()}, *two));
  EXPECT_TRUE(TightlySatisfies(Word{B(), B(), N()}, *two));
  EXPECT_TRUE(TightlySatisfies(Word{N(), B(), N(), B(), N(), N()}, *two));
  EXPECT_FALSE(TightlySatisfies(Word{B(), N()}, *two));
  EXPECT_FALSE(TightlySatisfies(Word{B(), B(), B()}, *two));

  auto one_to_two = SeqNonconsecutiveRange(b, 1, 2);
  EXPECT_TRUE(TightlySatisfies(Word{B(), N()}, *one_to_two));
  EXPECT_TRUE(TightlySatisfies(Word{N(), B(), B(), N()}, *one_to_two));
  EXPECT_FALSE(TightlySatisfies(Word{N(), N()}, *one_to_two));
  EXPECT_FALSE(TightlySatisfies(Word{B(), B(), B(), N()}, *one_to_two));

  auto two_or_more = SeqNonconsecutiveAtLeast(b, 2);
  EXPECT_TRUE(TightlySatisfies(Word{B(), B(), B(), N()}, *two_or_more));
  EXPECT_FALSE(TightlySatisfies(Word{B(), N(), N()}, *two_or_more));
}

}  // namespace
