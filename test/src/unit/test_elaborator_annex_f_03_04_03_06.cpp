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
