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

// §F.3.4.3.6 unfolds the followed_by operators into the negation of an
// implication over the negated consequent: (r #-# p) is (not (r |-> not p))
// over the §F.3.2 overlapping implication, and (r #=# p) is
// (not (r |=> not p)) over the §F.3.4.3.3 nonoverlapping one. The cases check
// that each factory builds the tree its identity names in both property
// models and that, under §F.5.3.1, a followed_by holds exactly where some
// match of the antecedent is followed by the consequent, so it fails rather
// than holds vacuously where the antecedent has no match.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const SequenceExpr> Atom(const std::string& name) {
  return SeqBoolean(BoolAtom(name));
}

// The overlapping form is the not of the implication whose antecedent is r
// itself and whose consequent is the not of p.
TEST(DerivedFollowedByOperators, OverlappingFormNegatesTheImplication) {
  auto p = PropStrong(Atom("b"));
  auto form = PropFollowedBy(Atom("a"), p);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kNot);
  ASSERT_NE(form->lhs, nullptr);
  const PropertyExpr& implication = *form->lhs;
  ASSERT_EQ(implication.kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(implication.sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*implication.sequence, *Atom("a")));
  ASSERT_NE(implication.lhs, nullptr);
  ASSERT_EQ(implication.lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(implication.lhs->lhs, p);
}

// The nonoverlapping form is the same over the §F.3.4.3.3 antecedent
// (r ##1 1), which is what parts it from the overlapping form.
TEST(DerivedFollowedByOperators,
     NonoverlappingFormNegatesTheNonoverlappingImplication) {
  auto p = PropStrong(Atom("b"));
  auto form = PropNonoverlappingFollowedBy(Atom("a"), p);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kNot);
  ASSERT_NE(form->lhs, nullptr);
  const PropertyExpr& implication = *form->lhs;
  ASSERT_EQ(implication.kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(implication.sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*implication.sequence,
                                *SeqConcat(Atom("a"), SeqBoolean(BoolTrue()))));
  EXPECT_FALSE(SequenceExprEqual(*implication.sequence, *Atom("a")));
  ASSERT_NE(implication.lhs, nullptr);
  ASSERT_EQ(implication.lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(implication.lhs->lhs, p);
}

// The clocked forms are the stated trees over the clocked operators, and the
// nonoverlapping one is not the overlapping one.
TEST(DerivedFollowedByOperators, ClockedFormsAreTheStatedTrees) {
  auto q = ClkStrong(Atom("b"));
  auto s = SeqClock(BoolAtom("clk"), Atom("a"));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkFollowedBy(s, q),
                                   *ClkNot(ClkImplication(s, ClkNot(q)))));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkNonoverlappingFollowedBy(s, q),
      *ClkNot(ClkNonoverlappingImplication(s, ClkNot(q)))));
  EXPECT_FALSE(ClockedPropertyEqual(*ClkNonoverlappingFollowedBy(s, q),
                                    *ClkFollowedBy(s, q)));
}

// Under §F.5.3.1, a #-# strong(b) holds where a match of a is followed by b
// on the same letter and fails where the letter with a lacks b; unlike
// a |-> strong(b), it fails on a letter without a, where the implication
// holds vacuously, and the negation of the consequent is the negation of
// strong(b), so a #-# not strong(b) holds where b is absent.
TEST(DerivedFollowedByOperators, OverlappingFormNeedsAMatchFollowedByP) {
  auto followed_by = PropFollowedBy(Atom("a"), PropStrong(Atom("b")));
  auto implication = PropImplication(Atom("a"), PropStrong(Atom("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a", "b"})}, *followed_by));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *followed_by));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *followed_by));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"})}, *followed_by));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"})}, *implication));
  auto negated = PropFollowedBy(Atom("a"), PropNot(PropStrong(Atom("b"))));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *negated));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a", "b"})}, *negated));
}

// The nonoverlapping form needs b on the letter after a: it holds on a then
// b, fails on a then a letter without b, and, unlike a |=> strong(b), fails
// on a lone a, whose one letter is too short for any match of (a ##1 1), and
// on a word without a.
TEST(DerivedFollowedByOperators, NonoverlappingFormStartsPOneLetterLater) {
  auto followed_by =
      PropNonoverlappingFollowedBy(Atom("a"), PropStrong(Atom("b")));
  auto implication =
      PropNonoverlappingImplication(Atom("a"), PropStrong(Atom("b")));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *followed_by));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a", "b"}), A({"x"})}, *followed_by));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"x"})}, *followed_by));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *followed_by));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"})}, *implication));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"x"}), A({"b"})}, *followed_by));
}

// In the clocked model under @(clk), a #=# strong(b) holds where a at one
// tick is followed, after an unclocked letter, by b at the next tick, which
// a #-# strong(b), judged from the letter with a, does not; b absent at the
// next tick fails both, and so does a word with no tick carrying a.
TEST(DerivedFollowedByOperators, UnderAClockTheConsequentWaitsATick) {
  auto clk = BoolAtom("clk");
  auto nonoverlapping = ClkClock(
      clk, ClkNonoverlappingFollowedBy(Atom("a"), ClkStrong(Atom("b"))));
  auto overlapping =
      ClkClock(clk, ClkFollowedBy(Atom("a"), ClkStrong(Atom("b"))));
  const Word kNextTickHasB{A({"clk", "a"}), A({"x"}), A({"clk", "b"})};
  const Word kNextTickLacksB{A({"clk", "a"}), A({"x"}), A({"clk", "x"})};
  const Word kNoTickHasA{A({"clk", "x"}), A({"a"}), A({"clk", "b"})};
  EXPECT_TRUE(
      NeutrallySatisfiesClockedProperty(kNextTickHasB, *nonoverlapping));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(kNextTickHasB, *overlapping));
  EXPECT_FALSE(
      NeutrallySatisfiesClockedProperty(kNextTickLacksB, *nonoverlapping));
  EXPECT_FALSE(
      NeutrallySatisfiesClockedProperty(kNextTickLacksB, *overlapping));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(kNoTickHasA, *nonoverlapping));
  EXPECT_FALSE(NeutrallySatisfiesClockedProperty(kNoTickHasA, *overlapping));
}

}  // namespace
