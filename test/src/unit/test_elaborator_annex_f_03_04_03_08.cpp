#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>

#include "elaborator/annex_f_derived_forms.h"
#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const SequenceExpr> Atom(const std::string& name) {
  return SeqBoolean(BoolAtom(name));
}

std::shared_ptr<const BooleanExpr> Zero() { return BoolNot(BoolTrue()); }

TEST(DerivedUnboundedTemporalOperators, AlwaysIsTheUntilReleasedByZero) {
  auto p = PropStrong(Atom("a"));
  auto form = PropAlways(p);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kUntil);
  EXPECT_EQ(form->lhs, p);
  ASSERT_NE(form->rhs, nullptr);
  ASSERT_EQ(form->rhs->kind, PropertyExpr::Kind::kStrong);
  ASSERT_NE(form->rhs->sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*form->rhs->sequence, *SeqBoolean(Zero())));
  EXPECT_FALSE(
      SequenceExprEqual(*form->rhs->sequence, *SeqBoolean(BoolTrue())));
}

TEST(DerivedUnboundedTemporalOperators, SEventuallyNegatesTheAlwaysOfNotP) {
  auto p = PropStrong(Atom("a"));
  auto form = PropSEventually(p);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kNot);
  ASSERT_NE(form->lhs, nullptr);
  ASSERT_EQ(form->lhs->kind, PropertyExpr::Kind::kUntil);
  ASSERT_NE(form->lhs->lhs, nullptr);
  ASSERT_EQ(form->lhs->lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(form->lhs->lhs->lhs, p);
  ASSERT_NE(form->lhs->rhs, nullptr);
  EXPECT_EQ(form->lhs->rhs->kind, PropertyExpr::Kind::kStrong);
}

TEST(DerivedUnboundedTemporalOperators, TheUntilFormsAreTheStatedTrees) {
  auto p = PropStrong(Atom("a"));
  auto q = PropStrong(Atom("b"));
  auto s_until = PropSUntil(p, q);
  ASSERT_EQ(s_until->kind, PropertyExpr::Kind::kAnd);
  ASSERT_NE(s_until->lhs, nullptr);
  ASSERT_EQ(s_until->lhs->kind, PropertyExpr::Kind::kUntil);
  EXPECT_EQ(s_until->lhs->lhs, p);
  EXPECT_EQ(s_until->lhs->rhs, q);
  ASSERT_NE(s_until->rhs, nullptr);
  ASSERT_EQ(s_until->rhs->kind, PropertyExpr::Kind::kNot);
  ASSERT_EQ(s_until->rhs->lhs->kind, PropertyExpr::Kind::kUntil);
  EXPECT_EQ(s_until->rhs->lhs->lhs->lhs, q);

  auto until_with = PropUntilWith(p, q);
  ASSERT_EQ(until_with->kind, PropertyExpr::Kind::kUntil);
  EXPECT_EQ(until_with->lhs, p);
  ASSERT_NE(until_with->rhs, nullptr);
  ASSERT_EQ(until_with->rhs->kind, PropertyExpr::Kind::kAnd);
  EXPECT_EQ(until_with->rhs->lhs, p);
  EXPECT_EQ(until_with->rhs->rhs, q);

  auto s_until_with = PropSUntilWith(p, q);
  ASSERT_EQ(s_until_with->kind, PropertyExpr::Kind::kAnd);
  ASSERT_EQ(s_until_with->lhs->kind, PropertyExpr::Kind::kUntil);
  EXPECT_EQ(s_until_with->lhs->lhs, p);
  ASSERT_EQ(s_until_with->lhs->rhs->kind, PropertyExpr::Kind::kAnd);
  EXPECT_EQ(s_until_with->lhs->rhs->lhs, p);
  EXPECT_EQ(s_until_with->lhs->rhs->rhs, q);
  ASSERT_EQ(s_until_with->rhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(s_until_with->rhs->lhs->lhs->lhs, s_until_with->lhs->rhs);
}

TEST(DerivedUnboundedTemporalOperators, ClockedFormsAreTheStatedTrees) {
  auto q1 = ClkStrong(Atom("a"));
  auto q2 = ClkStrong(Atom("b"));
  auto always = ClkUntil(q1, ClkBoolean(Zero()));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkAlways(q1), *always));
  EXPECT_FALSE(ClockedPropertyEqual(*ClkAlways(q1),
                                    *ClkUntil(q1, ClkBoolean(BoolTrue()))));
  auto s_eventually = ClkNot(ClkUntil(ClkNot(q2), ClkBoolean(Zero())));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkSEventually(q2), *s_eventually));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkSUntil(q1, q2),
                                   *ClkAnd(ClkUntil(q1, q2), s_eventually)));
  EXPECT_FALSE(ClockedPropertyEqual(*ClkSUntil(q1, q2), *ClkUntil(q1, q2)));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkUntilWith(q1, q2),
                                   *ClkUntil(q1, ClkAnd(q1, q2))));
  EXPECT_FALSE(ClockedPropertyEqual(*ClkUntilWith(q1, q2), *ClkUntil(q1, q2)));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkSUntilWith(q1, q2),
                                   *ClkSUntil(q1, ClkAnd(q1, q2))));
}

TEST(DerivedUnboundedTemporalOperators,
     AlwaysNeedsEveryLetterAndSEventuallySome) {
  auto always = PropAlways(PropStrong(Atom("a")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *always));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"a", "b"})}, *always));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *always));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"b"}), A({"a"})}, *always));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"b"}), A({"a"})}, *always));

  auto s_eventually = PropSEventually(PropStrong(Atom("a")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *s_eventually));
  EXPECT_TRUE(
      NeutrallySatisfies(Word{A({"b"}), A({"b"}), A({"a"})}, *s_eventually));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"b"}), A({"b"})}, *s_eventually));
}

TEST(DerivedUnboundedTemporalOperators, SUntilNeedsTheRelease) {
  auto p = PropStrong(Atom("a"));
  auto q = PropStrong(Atom("b"));
  auto s_until = PropSUntil(p, q);
  auto until = PropUntil(p, q);
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"a"}), A({"b"})}, *s_until));
  EXPECT_FALSE(
      NeutrallySatisfies(Word{A({"a"}), A({"c"}), A({"b"})}, *s_until));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"a"})}, *s_until));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"a"})}, *until));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"b"})}, *s_until));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"c"})}, *s_until));
}

TEST(DerivedUnboundedTemporalOperators, TheWithFormsNeedPAtTheRelease) {
  auto p = PropStrong(Atom("a"));
  auto q = PropStrong(Atom("b"));
  auto until_with = PropUntilWith(p, q);
  auto until = PropUntil(p, q);
  auto s_until_with = PropSUntilWith(p, q);
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"a", "b"})}, *until_with));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *until_with));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *until));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"a"})}, *until_with));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"a"})}, *s_until_with));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"a", "b"})}, *s_until_with));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *s_until_with));
}

TEST(DerivedUnboundedTemporalOperators, UnderAClockOnlyTheTicksCount) {
  auto clk = BoolAtom("clk");
  auto always = ClkClock(clk, ClkAlways(ClkStrong(Atom("a"))));
  auto s_eventually = ClkClock(clk, ClkSEventually(ClkStrong(Atom("a"))));
  const Word kEveryTickHasA{A({"clk", "a"}), A({"b"}), A({"clk", "a"})};
  const Word kSecondTickLacksA{A({"clk", "a"}), A({"a"}), A({"clk", "b"})};
  const Word kOnlyAnUnclockedLetterHasA{A({"clk", "b"}), A({"a"}),
                                        A({"clk", "b"})};
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(kEveryTickHasA, *always));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(kSecondTickLacksA, *always));
  EXPECT_FALSE(
      NeutrallySatisfiesClockedProperty(kOnlyAnUnclockedLetterHasA, *always));
  EXPECT_TRUE(NeutrallySatisfiesClockedProperty(kEveryTickHasA, *s_eventually));
  EXPECT_TRUE(
      NeutrallySatisfiesClockedProperty(kSecondTickLacksA, *s_eventually));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(kOnlyAnUnclockedLetterHasA,
                                                 *s_eventually));
  EXPECT_TRUE(NeutrallySatisfies(kOnlyAnUnclockedLetterHasA,
                                 *PropSEventually(PropStrong(Atom("a")))));
}

}  // namespace
