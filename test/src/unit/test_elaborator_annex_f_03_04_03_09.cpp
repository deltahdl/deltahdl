#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

// §F.3.4.3.9 unfolds the bounded temporal operators into the §F.3.2 nexttime,
// implication, not, or and and over the §F.3.4.3.8 always and s_eventually:
// (s_nexttime p) is (not nexttime not p), (nexttime[0] p) is (1 |-> p),
// (nexttime[m] p) is (nexttime (nexttime[m-1] p)), (s_nexttime[m] p) is
// (not nexttime[m] not p), eventually[m:n] is the or of nexttime[m] through
// nexttime[n], always[m:n] their and, (always[m:$] p) is
// (nexttime[m] always p), (s_eventually[m:n] p) is (not always[m:n] not p),
// (s_eventually[m:$] p) is (s_nexttime[m] s_eventually p), and
// (s_always[m:n] p) is (not eventually[m:n] not p). The cases check that
// each factory builds the tree its identity names in both property models
// and that, under §F.5.3.1, the weak forms hold where the word ends before
// the letter they name while the strong forms need that letter, and that a
// clock counts ticks rather than letters.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const SequenceExpr> Atom(const std::string& name) {
  return SeqBoolean(BoolAtom(name));
}

// (s_nexttime p) is the negation of the nexttime over the negation of p.
TEST(DerivedBoundedTemporalOperators, SNexttimeNegatesTheNexttimeOfNotP) {
  auto p = PropStrong(Atom("a"));
  auto form = PropSNexttime(p);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kNot);
  ASSERT_NE(form->lhs, nullptr);
  ASSERT_EQ(form->lhs->kind, PropertyExpr::Kind::kNexttime);
  ASSERT_NE(form->lhs->lhs, nullptr);
  ASSERT_EQ(form->lhs->lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(form->lhs->lhs->lhs, p);
}

// (nexttime[0] p) is the implication whose antecedent is the sequence 1 and
// whose consequent is p, and (nexttime[m] p) wraps that in m nexttimes, so
// nexttime[2] is nexttime over nexttime over the implication rather than
// over p itself.
TEST(DerivedBoundedTemporalOperators, NexttimeCountIsNexttimesOverOneImpliesP) {
  auto p = PropStrong(Atom("a"));
  auto zero = PropNexttimeExactly(p, 0);
  ASSERT_EQ(zero->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(zero->sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*zero->sequence, *SeqBoolean(BoolTrue())));
  EXPECT_EQ(zero->lhs, p);
  auto two = PropNexttimeExactly(p, 2);
  ASSERT_EQ(two->kind, PropertyExpr::Kind::kNexttime);
  ASSERT_NE(two->lhs, nullptr);
  ASSERT_EQ(two->lhs->kind, PropertyExpr::Kind::kNexttime);
  ASSERT_NE(two->lhs->lhs, nullptr);
  ASSERT_EQ(two->lhs->lhs->kind, PropertyExpr::Kind::kImplication);
  EXPECT_EQ(two->lhs->lhs->lhs, p);
}

// (s_nexttime[m] p) is the negation of nexttime[m] over the negation of p.
TEST(DerivedBoundedTemporalOperators, SNexttimeCountNegatesTheCountOfNotP) {
  auto p = PropStrong(Atom("a"));
  auto form = PropSNexttimeExactly(p, 1);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kNot);
  ASSERT_NE(form->lhs, nullptr);
  ASSERT_EQ(form->lhs->kind, PropertyExpr::Kind::kNexttime);
  ASSERT_NE(form->lhs->lhs, nullptr);
  ASSERT_EQ(form->lhs->lhs->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(form->lhs->lhs->lhs, nullptr);
  ASSERT_EQ(form->lhs->lhs->lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(form->lhs->lhs->lhs->lhs, p);
}

// eventually[m:m] and always[m:m] are nexttime[m] alone; a wider range is
// the or, or the and, of the narrower range with nexttime[n], so [0:2]
// is (([0] or [1]) or [2]) and (([0] and [1]) and [2]).
TEST(DerivedBoundedTemporalOperators, RangesFoldTheCountsFromTheLeft) {
  auto p = PropStrong(Atom("a"));
  auto meeting = PropEventuallyRange(p, 1, 1);
  ASSERT_EQ(meeting->kind, PropertyExpr::Kind::kNexttime);
  ASSERT_NE(meeting->lhs, nullptr);
  EXPECT_EQ(meeting->lhs->kind, PropertyExpr::Kind::kImplication);
  EXPECT_EQ(PropAlwaysRange(p, 1, 1)->kind, PropertyExpr::Kind::kNexttime);

  auto eventually = PropEventuallyRange(p, 0, 2);
  ASSERT_EQ(eventually->kind, PropertyExpr::Kind::kOr);
  ASSERT_NE(eventually->lhs, nullptr);
  ASSERT_EQ(eventually->lhs->kind, PropertyExpr::Kind::kOr);
  ASSERT_NE(eventually->lhs->lhs, nullptr);
  EXPECT_EQ(eventually->lhs->lhs->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(eventually->lhs->rhs, nullptr);
  EXPECT_EQ(eventually->lhs->rhs->kind, PropertyExpr::Kind::kNexttime);
  ASSERT_NE(eventually->rhs, nullptr);
  ASSERT_EQ(eventually->rhs->kind, PropertyExpr::Kind::kNexttime);
  ASSERT_NE(eventually->rhs->lhs, nullptr);
  ASSERT_EQ(eventually->rhs->lhs->kind, PropertyExpr::Kind::kNexttime);
  ASSERT_NE(eventually->rhs->lhs->lhs, nullptr);
  EXPECT_EQ(eventually->rhs->lhs->lhs->lhs, p);

  auto always = PropAlwaysRange(p, 0, 2);
  ASSERT_EQ(always->kind, PropertyExpr::Kind::kAnd);
  ASSERT_NE(always->lhs, nullptr);
  ASSERT_EQ(always->lhs->kind, PropertyExpr::Kind::kAnd);
  ASSERT_NE(always->lhs->lhs, nullptr);
  EXPECT_EQ(always->lhs->lhs->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(always->rhs, nullptr);
  EXPECT_EQ(always->rhs->kind, PropertyExpr::Kind::kNexttime);
}

// (always[m:$] p) is nexttime[m] over the §F.3.4.3.8 always, whose left
// operand is p; (s_eventually[m:n] p) and (s_always[m:n] p) negate the
// opposite range over not p; and (s_eventually[m:$] p) is s_nexttime[m]
// over the §F.3.4.3.8 s_eventually.
TEST(DerivedBoundedTemporalOperators,
     TheUnboundedAndStrongFormsAreTheStatedTrees) {
  auto p = PropStrong(Atom("a"));
  auto always_at_least = PropAlwaysAtLeast(p, 1);
  ASSERT_EQ(always_at_least->kind, PropertyExpr::Kind::kNexttime);
  ASSERT_NE(always_at_least->lhs, nullptr);
  ASSERT_EQ(always_at_least->lhs->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(always_at_least->lhs->lhs, nullptr);
  ASSERT_EQ(always_at_least->lhs->lhs->kind, PropertyExpr::Kind::kUntil);
  EXPECT_EQ(always_at_least->lhs->lhs->lhs, p);

  auto s_eventually = PropSEventuallyRange(p, 0, 1);
  ASSERT_EQ(s_eventually->kind, PropertyExpr::Kind::kNot);
  ASSERT_NE(s_eventually->lhs, nullptr);
  ASSERT_EQ(s_eventually->lhs->kind, PropertyExpr::Kind::kAnd);
  ASSERT_NE(s_eventually->lhs->lhs, nullptr);
  ASSERT_EQ(s_eventually->lhs->lhs->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(s_eventually->lhs->lhs->lhs, nullptr);
  ASSERT_EQ(s_eventually->lhs->lhs->lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(s_eventually->lhs->lhs->lhs->lhs, p);

  auto s_always = PropSAlwaysRange(p, 0, 1);
  ASSERT_EQ(s_always->kind, PropertyExpr::Kind::kNot);
  ASSERT_NE(s_always->lhs, nullptr);
  ASSERT_EQ(s_always->lhs->kind, PropertyExpr::Kind::kOr);
  ASSERT_NE(s_always->lhs->lhs, nullptr);
  ASSERT_EQ(s_always->lhs->lhs->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(s_always->lhs->lhs->lhs, nullptr);
  ASSERT_EQ(s_always->lhs->lhs->lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(s_always->lhs->lhs->lhs->lhs, p);

  auto s_eventually_at_least = PropSEventuallyAtLeast(p, 1);
  ASSERT_EQ(s_eventually_at_least->kind, PropertyExpr::Kind::kNot);
  const PropertyExpr* node = s_eventually_at_least->lhs.get();
  ASSERT_NE(node, nullptr);
  ASSERT_EQ(node->kind, PropertyExpr::Kind::kNexttime);
  node = node->lhs.get();
  ASSERT_NE(node, nullptr);
  ASSERT_EQ(node->kind, PropertyExpr::Kind::kImplication);
  node = node->lhs.get();
  ASSERT_NE(node, nullptr);
  ASSERT_EQ(node->kind, PropertyExpr::Kind::kNot);
  node = node->lhs.get();
  ASSERT_NE(node, nullptr);
  ASSERT_EQ(node->kind, PropertyExpr::Kind::kNot);
  node = node->lhs.get();
  ASSERT_NE(node, nullptr);
  ASSERT_EQ(node->kind, PropertyExpr::Kind::kUntil);
  ASSERT_NE(node->lhs, nullptr);
  ASSERT_EQ(node->lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(node->lhs->lhs, p);
}

// The clocked forms are the same trees over the clocked primitives, with the
// antecedent of nexttime[0] the bare Boolean sequence 1; nexttime[2] q is
// not two nexttimes over q itself, and the eventually range is not the
// always range.
TEST(DerivedBoundedTemporalOperators, ClockedFormsAreTheStatedTrees) {
  auto q = ClkStrong(Atom("a"));
  auto one = SeqBoolean(BoolTrue());
  EXPECT_TRUE(
      ClockedPropertyEqual(*ClkSNexttime(q), *ClkNot(ClkNexttime(ClkNot(q)))));
  EXPECT_TRUE(
      ClockedPropertyEqual(*ClkNexttimeExactly(q, 0), *ClkImplication(one, q)));
  EXPECT_TRUE(
      ClockedPropertyEqual(*ClkNexttimeExactly(q, 2),
                           *ClkNexttime(ClkNexttime(ClkImplication(one, q)))));
  EXPECT_FALSE(ClockedPropertyEqual(*ClkNexttimeExactly(q, 2),
                                    *ClkNexttime(ClkNexttime(q))));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkSNexttimeExactly(q, 1),
      *ClkNot(ClkNexttime(ClkImplication(one, ClkNot(q))))));
  auto n0 = ClkNexttimeExactly(q, 0);
  auto n1 = ClkNexttimeExactly(q, 1);
  auto n2 = ClkNexttimeExactly(q, 2);
  EXPECT_TRUE(ClockedPropertyEqual(*ClkEventuallyRange(q, 1, 1), *n1));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkEventuallyRange(q, 0, 2),
                                   *ClkOr(ClkOr(n0, n1), n2)));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkAlwaysRange(q, 0, 2),
                                   *ClkAnd(ClkAnd(n0, n1), n2)));
  EXPECT_FALSE(ClockedPropertyEqual(*ClkAlwaysRange(q, 0, 2),
                                    *ClkEventuallyRange(q, 0, 2)));
  EXPECT_TRUE(
      ClockedPropertyEqual(*ClkAlwaysAtLeast(q, 1),
                           *ClkNexttime(ClkImplication(one, ClkAlways(q)))));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkSEventuallyRange(q, 0, 1),
      *ClkNot(ClkAnd(ClkImplication(one, ClkNot(q)),
                     ClkNexttime(ClkImplication(one, ClkNot(q)))))));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkSEventuallyAtLeast(q, 1),
      *ClkNot(ClkNexttime(ClkImplication(one, ClkNot(ClkSEventually(q)))))));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkSAlwaysRange(q, 0, 1),
      *ClkNot(ClkOr(ClkImplication(one, ClkNot(q)),
                    ClkNexttime(ClkImplication(one, ClkNot(q)))))));
}

// Under §F.5.3.1, nexttime[1] strong(a) holds on a lone letter, because the
// (1 |-> p) at the base of the identity holds on the empty suffix where the
// bare nexttime strong(a) of §F.3.2, judging strong(a) there, does not; the
// strong forms s_nexttime and s_nexttime[1] fail on the lone letter; and all
// four need a on the second letter where there is one. nexttime[0] strong(a)
// needs a on the first letter and holds on the empty word; nexttime[2]
// strong(a) needs a on the third letter and holds on a word of two, where
// s_nexttime[2] fails.
TEST(DerivedBoundedTemporalOperators, TheStrongNexttimesNeedTheLetterTheyName) {
  auto p = PropStrong(Atom("a"));
  auto bare = PropNexttime(p);
  auto one = PropNexttimeExactly(p, 1);
  auto strong = PropSNexttime(p);
  auto strong_one = PropSNexttimeExactly(p, 1);
  const Word kLoneLetter{A({"b"})};
  const Word kSecondHasA{A({"b"}), A({"a"})};
  const Word kSecondLacksA{A({"a"}), A({"b"})};
  EXPECT_TRUE(NeutrallySatisfies(kLoneLetter, *one));
  EXPECT_FALSE(NeutrallySatisfies(kLoneLetter, *bare));
  EXPECT_FALSE(NeutrallySatisfies(kLoneLetter, *strong));
  EXPECT_FALSE(NeutrallySatisfies(kLoneLetter, *strong_one));
  EXPECT_TRUE(NeutrallySatisfies(kSecondHasA, *one));
  EXPECT_TRUE(NeutrallySatisfies(kSecondHasA, *strong));
  EXPECT_TRUE(NeutrallySatisfies(kSecondHasA, *strong_one));
  EXPECT_FALSE(NeutrallySatisfies(kSecondLacksA, *one));
  EXPECT_FALSE(NeutrallySatisfies(kSecondLacksA, *strong));
  EXPECT_FALSE(NeutrallySatisfies(kSecondLacksA, *strong_one));

  auto zero = PropNexttimeExactly(p, 0);
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *zero));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"b"})}, *zero));
  EXPECT_TRUE(NeutrallySatisfies(Word{}, *zero));
  auto two = PropNexttimeExactly(p, 2);
  auto strong_two = PropSNexttimeExactly(p, 2);
  const Word kThirdHasA{A({"b"}), A({"b"}), A({"a"})};
  const Word kOnlyTheSecondHasA{A({"b"}), A({"a"}), A({"b"})};
  const Word kTwoLetters{A({"b"}), A({"b"})};
  EXPECT_TRUE(NeutrallySatisfies(kThirdHasA, *two));
  EXPECT_TRUE(NeutrallySatisfies(kThirdHasA, *strong_two));
  EXPECT_FALSE(NeutrallySatisfies(kOnlyTheSecondHasA, *two));
  EXPECT_FALSE(NeutrallySatisfies(kOnlyTheSecondHasA, *strong_two));
  EXPECT_TRUE(NeutrallySatisfies(kTwoLetters, *two));
  EXPECT_FALSE(NeutrallySatisfies(kTwoLetters, *strong_two));
}

// eventually[1:2] strong(a) holds where a is on the second or third letter
// and, being weak, where the word has no third letter; s_eventually[1:2]
// needs the a. always[1:2] strong(a) needs a on both letters where both are
// there and holds where the third is missing; s_always[1:2] fails there.
TEST(DerivedBoundedTemporalOperators, TheRangesNameTheLettersTheySpan) {
  auto p = PropStrong(Atom("a"));
  auto eventually = PropEventuallyRange(p, 1, 2);
  auto s_eventually = PropSEventuallyRange(p, 1, 2);
  auto always = PropAlwaysRange(p, 1, 2);
  auto s_always = PropSAlwaysRange(p, 1, 2);
  const Word kSecondHasA{A({"b"}), A({"a"}), A({"b"})};
  const Word kThirdHasA{A({"b"}), A({"b"}), A({"a"})};
  const Word kBothHaveA{A({"b"}), A({"a"}), A({"a"})};
  const Word kNeitherHasA{A({"a"}), A({"b"}), A({"b"})};
  const Word kNoThirdLetter{A({"b"}), A({"a"})};
  const Word kNoThirdLetterNoA{A({"b"}), A({"b"})};
  EXPECT_TRUE(NeutrallySatisfies(kSecondHasA, *eventually));
  EXPECT_TRUE(NeutrallySatisfies(kThirdHasA, *eventually));
  EXPECT_FALSE(NeutrallySatisfies(kNeitherHasA, *eventually));
  EXPECT_TRUE(NeutrallySatisfies(kNoThirdLetterNoA, *eventually));
  EXPECT_TRUE(NeutrallySatisfies(kSecondHasA, *s_eventually));
  EXPECT_TRUE(NeutrallySatisfies(kThirdHasA, *s_eventually));
  EXPECT_FALSE(NeutrallySatisfies(kNeitherHasA, *s_eventually));
  EXPECT_FALSE(NeutrallySatisfies(kNoThirdLetterNoA, *s_eventually));
  EXPECT_TRUE(NeutrallySatisfies(kNoThirdLetter, *s_eventually));
  EXPECT_TRUE(NeutrallySatisfies(kBothHaveA, *always));
  EXPECT_FALSE(NeutrallySatisfies(kSecondHasA, *always));
  EXPECT_FALSE(NeutrallySatisfies(kThirdHasA, *always));
  EXPECT_TRUE(NeutrallySatisfies(kNoThirdLetter, *always));
  EXPECT_TRUE(NeutrallySatisfies(kBothHaveA, *s_always));
  EXPECT_FALSE(NeutrallySatisfies(kSecondHasA, *s_always));
  EXPECT_FALSE(NeutrallySatisfies(kNoThirdLetter, *s_always));
}

// always[1:$] strong(a) needs a from the second letter on and holds on a lone
// letter; s_eventually[1:$] strong(a) needs a on some letter after the first
// and fails on a lone letter, on a word without a, and where a is only on
// the first letter.
TEST(DerivedBoundedTemporalOperators, TheUnboundedFormsStartAtTheCount) {
  auto p = PropStrong(Atom("a"));
  auto always = PropAlwaysAtLeast(p, 1);
  auto s_eventually = PropSEventuallyAtLeast(p, 1);
  const Word kAFromTheSecond{A({"b"}), A({"a"}), A({"a"})};
  const Word kAOnlyOnTheSecond{A({"b"}), A({"a"}), A({"b"})};
  const Word kAOnlyOnTheThird{A({"b"}), A({"b"}), A({"a"})};
  const Word kAOnlyOnTheFirst{A({"a"}), A({"b"})};
  const Word kLoneLetter{A({"b"})};
  EXPECT_TRUE(NeutrallySatisfies(kAFromTheSecond, *always));
  EXPECT_FALSE(NeutrallySatisfies(kAOnlyOnTheSecond, *always));
  EXPECT_FALSE(NeutrallySatisfies(kAOnlyOnTheThird, *always));
  EXPECT_TRUE(NeutrallySatisfies(kLoneLetter, *always));
  EXPECT_TRUE(NeutrallySatisfies(kAFromTheSecond, *s_eventually));
  EXPECT_TRUE(NeutrallySatisfies(kAOnlyOnTheThird, *s_eventually));
  EXPECT_FALSE(NeutrallySatisfies(kAOnlyOnTheFirst, *s_eventually));
  EXPECT_FALSE(NeutrallySatisfies(kLoneLetter, *s_eventually));
}

// In the clocked model under @(clk), nexttime[1] strong(a) is judged at the
// second tick, so a on an unclocked letter between the ticks does not count,
// and where the word ends before a second tick the weak nexttime[1] holds
// and s_nexttime[1] fails.
TEST(DerivedBoundedTemporalOperators, UnderAClockTheCountIsInTicks) {
  auto clk = BoolAtom("clk");
  auto weak = ClkClock(clk, ClkNexttimeExactly(ClkStrong(Atom("a")), 1));
  auto strong = ClkClock(clk, ClkSNexttimeExactly(ClkStrong(Atom("a")), 1));
  const Word kSecondTickHasA{A({"clk", "b"}), A({"x"}), A({"clk", "a"})};
  const Word kOnlyAnUnclockedLetterHasA{A({"clk", "b"}), A({"a"}),
                                        A({"clk", "b"})};
  const Word kOnlyTheFirstTickHasA{A({"clk", "a"}), A({"x"}), A({"clk", "b"})};
  const Word kNoSecondTick{A({"clk", "b"}), A({"a"})};
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(kSecondTickHasA, *weak));
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(kSecondTickHasA, *strong));
  EXPECT_FALSE(
      NeutrallySatisfiesClockedProperty(kOnlyAnUnclockedLetterHasA, *weak));
  EXPECT_FALSE(
      NeutrallySatisfiesClockedProperty(kOnlyAnUnclockedLetterHasA, *strong));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(kOnlyTheFirstTickHasA, *weak));
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(kNoSecondTick, *weak));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(kNoSecondTick, *strong));
  EXPECT_TRUE(
      NeutrallySatisfies(kOnlyAnUnclockedLetterHasA,
                         *PropNexttimeExactly(PropStrong(Atom("a")), 1)));
}

}  // namespace
