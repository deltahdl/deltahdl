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

// §F.3.4.3.8 unfolds the unbounded temporal operators into the §F.3.2 until,
// not and and: (always p) is (p until 0), (s_eventually p) is
// (not (always (not p))), (p s_until q) is ((p until q) and s_eventually q),
// (p until_with q) is (p until (p and q)), and (p s_until_with q) is
// (p s_until (p and q)). The cases check that each factory builds the tree
// its identity names in both property models and that, under §F.5.3.1,
// always requires p from every letter, s_eventually from some letter, s_until
// parts from until where q never releases it, and the with forms require p at
// the releasing letter as well.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const SequenceExpr> Atom(const std::string& name) {
  return SeqBoolean(BoolAtom(name));
}

// The Boolean 0 the always identity releases on, as the §F.3.2 Boolean !1.
std::shared_ptr<const BooleanExpr> Zero() { return BoolNot(BoolTrue()); }

// (always p) is the until whose left operand is p and whose release is the
// Boolean 0, read as strong(0) in the unclocked model.
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

// (s_eventually p) is the negation of the always over the negation of p.
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

// (p s_until q) is the and of (p until q) with (s_eventually q); the with
// forms release on (p and q), the strong one over the s_until tree.
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

// The clocked forms are the same trees over the clocked until, with the
// Boolean property 0 as the release of the always; the strong until is not
// the plain one and the with form is not the plain until.
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

// Under §F.5.3.1, always strong(a) holds where every letter carries a and
// fails where one does not, whatever its position; s_eventually strong(a)
// holds where some letter carries a and fails where none does.
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

// strong(a) s_until strong(b) holds on a, a, b and fails on a, c, b, where a
// lapses before b releases it, and on a, a, where b never does; the plain
// until holds on a, a, which is where the two part.
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

// strong(a) until_with strong(b) needs a on the letter with b: it holds on a
// then a and b together, fails on a then b alone, where the plain until holds,
// and holds on a, a with no b at all; the strong form fails there and agrees
// on the other two.
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

// In the clocked model under @(clk), always strong(a) requires a at every
// clk tick and nothing at the unclocked letters between them, and
// s_eventually strong(a) requires a at some tick, so a carried only by an
// unclocked letter satisfies neither where the unclocked s_eventually holds.
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
