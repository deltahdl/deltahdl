#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto BoolSeq(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

std::shared_ptr<const SequenceExpr> AnyRun() {
  return SeqRepeatAtLeast(SeqBoolean(BoolTrue()), 0);
}

TEST(DerivedSequenceOperators, AndMatchesBothFromOneLetterToTheLongerEnd) {
  auto ab = SeqConcat(BoolSeq("a"), BoolSeq("b"));
  auto c = BoolSeq("c");
  EXPECT_TRUE(SequenceExprEqual(
      *SeqAnd(ab, c), *SeqOr(SeqIntersect(SeqConcat(ab, AnyRun()), c),
                             SeqIntersect(ab, SeqConcat(c, AnyRun())))));

  auto ab_and_c = SeqAnd(ab, c);
  EXPECT_TRUE(TightlySatisfies(Word{A({"a", "c"}), A({"b"})}, *ab_and_c));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a"}), A({"b", "c"})}, *ab_and_c));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a", "c"})}, *ab_and_c));

  auto a_and_cd = SeqAnd(BoolSeq("a"), SeqConcat(c, BoolSeq("d")));
  EXPECT_TRUE(TightlySatisfies(Word{A({"a", "c"}), A({"d"})}, *a_and_cd));
  EXPECT_FALSE(TightlySatisfies(Word{A({"c"}), A({"a", "d"})}, *a_and_cd));
}

TEST(DerivedSequenceOperators, WithinMatchesTheFirstInsideTheSecond) {
  auto a = BoolSeq("a");
  auto c = BoolSeq("c");
  auto ccc = SeqConcat(SeqConcat(c, c), c);
  EXPECT_TRUE(SequenceExprEqual(
      *SeqWithin(a, ccc),
      *SeqIntersect(SeqConcat(SeqConcat(AnyRun(), a), AnyRun()), ccc)));

  auto a_within_ccc = SeqWithin(a, ccc);
  EXPECT_TRUE(
      TightlySatisfies(Word{A({"c"}), A({"a", "c"}), A({"c"})}, *a_within_ccc));
  EXPECT_TRUE(
      TightlySatisfies(Word{A({"a", "c"}), A({"c"}), A({"c"})}, *a_within_ccc));
  EXPECT_TRUE(
      TightlySatisfies(Word{A({"c"}), A({"c"}), A({"a", "c"})}, *a_within_ccc));
  EXPECT_FALSE(
      TightlySatisfies(Word{A({"c"}), A({"c"}), A({"c"})}, *a_within_ccc));
  EXPECT_FALSE(
      TightlySatisfies(Word{A({"a"}), A({"c"}), A({"c"})}, *a_within_ccc));
  EXPECT_FALSE(TightlySatisfies(Word{A({"a", "c"}), A({"c"})}, *a_within_ccc));
}

TEST(DerivedSequenceOperators, ThroughoutHoldsTheBooleanAtEveryLetter) {
  auto b = BoolAtom("b");
  auto ac = SeqConcat(BoolSeq("a"), BoolSeq("c"));
  EXPECT_TRUE(
      SequenceExprEqual(*SeqThroughout(b, ac),
                        *SeqIntersect(SeqRepeatAtLeast(SeqBoolean(b), 0), ac)));

  auto b_throughout_ac = SeqThroughout(b, ac);
  EXPECT_TRUE(
      TightlySatisfies(Word{A({"a", "b"}), A({"b", "c"})}, *b_throughout_ac));
  EXPECT_FALSE(
      TightlySatisfies(Word{A({"a", "b"}), A({"c"})}, *b_throughout_ac));
  EXPECT_FALSE(
      TightlySatisfies(Word{A({"a"}), A({"b", "c"})}, *b_throughout_ac));
  EXPECT_FALSE(
      TightlySatisfies(Word{A({"a", "b"}), A({"b"})}, *b_throughout_ac));
}

TEST(DerivedSequenceOperators, MatchItemsFuseSamplingsOntoTheLastLetter) {
  auto ac = SeqConcat(BoolSeq("a"), BoolSeq("c"));
  auto one = SeqBoolean(BoolTrue());
  EXPECT_TRUE(SequenceExprEqual(*SeqWithLocalAssignments(ac, {"v"}),
                                *SeqFusion(ac, SeqLocalVarSampling("v"))));
  EXPECT_TRUE(SequenceExprEqual(
      *SeqWithLocalAssignments(ac, {"v", "u", "w"}),
      *SeqFusion(SeqFusion(ac, SeqLocalVarSampling("v")),
                 SeqFusion(SeqFusion(one, SeqLocalVarSampling("u")),
                           SeqFusion(one, SeqLocalVarSampling("w"))))));

  auto two = SeqWithLocalAssignments(ac, {"v", "u"});
  const Word kMatch{A({"a"}), A({"c"})};
  auto outputs = TightSatisfactionOutputs(kMatch, *two, LocalContext{});
  ASSERT_EQ(outputs.size(), 1u);
  EXPECT_TRUE(LocalContextEqual(
      outputs.front(), LocalContext{{"v", A({"c"})}, {"u", A({"c"})}}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"a"}), A({"d"})}, *two, LocalContext{})
          .empty());
}

}  // namespace
