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

Letter N() { return A({"a"}); }
Letter B() { return A({"b"}); }

std::shared_ptr<const SequenceExpr> Unit(
    const std::shared_ptr<const BooleanExpr>& b) {
  return SeqConcat(SeqRepeatAtLeast(SeqBoolean(BoolNot(b)), 0), SeqBoolean(b));
}

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
