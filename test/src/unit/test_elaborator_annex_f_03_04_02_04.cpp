#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

using namespace delta;

// §F.3.4.2.4 unfolds the remaining derived sequence operators: and, within
// and throughout into intersect with a padding of 1[*0:$] or a repetition of
// the Boolean, and a sequence match item list into fusions with the §F.3.2
// sampling form. Each case checks the tree a form unfolds to against the
// identity the subclause states, then the words that tightly satisfy it, under
// §F.5.2 for the first three and §F.5.5 for the local variable form.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

auto BoolSeq(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// 1[*0:$] in the §F.3.4.2.1 unfolding of [*0:$].
std::shared_ptr<const SequenceExpr> AnyRun() {
  return SeqRepeatAtLeast(SeqBoolean(BoolTrue()), 0);
}

// (R1 and R2) is (((R1 ##1 1[*0:$]) intersect R2) or (R1 intersect (R2 ##1
// 1[*0:$]))): (a ##1 b) and c is matched by a c then b, where c ends first,
// and a and (c ##1 d) by a c then d, where a ends first; neither by a word
// whose operands start at different letters.
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

// (R1 within R2) is ((1[*0:$] ##1 R1 ##1 1[*0:$]) intersect R2): a within
// (c ##1 c ##1 c) is matched by three letters c with a at any of them, and not
// by three letters c without a or by a word that is not three letters c.
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

// (b throughout R) is ((b[*0:$]) intersect R): b throughout (a ##1 c) is
// matched by a then c with b at both letters and not with b missing at either.
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

// (R, v = e) is (R ##0 (1, v = e)) and (R, v1 = e1, ..., vk = ek) is
// ((R, v1 = e1) ##0 (1, v2 = e2, ..., vk = ek)): under §F.5.5 the match of
// a ##1 c with two assignments binds both names to the letter the match ends
// at, and a word that does not match R binds nothing.
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
