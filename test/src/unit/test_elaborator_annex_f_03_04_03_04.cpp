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

TEST(DerivedConditionalOperators, UnclockedIfIsAnImplicationOverTheBoolean) {
  auto p = PropStrong(Atom("b"));
  auto form = PropIf(BoolAtom("a"), p);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(form->sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*form->sequence, *Atom("a")));
  EXPECT_EQ(form->lhs, p);
}

TEST(DerivedConditionalOperators, UnclockedIfElseIsTheStatedConjunction) {
  auto p1 = PropStrong(Atom("b"));
  auto p2 = PropStrong(Atom("c"));
  auto form = PropIfElse(BoolAtom("a"), p1, p2);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kAnd);
  ASSERT_NE(form->lhs, nullptr);
  ASSERT_NE(form->rhs, nullptr);
  const PropertyExpr& then_branch = *form->lhs;
  ASSERT_EQ(then_branch.kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(then_branch.sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*then_branch.sequence, *Atom("a")));
  EXPECT_EQ(then_branch.lhs, p1);
  const PropertyExpr& else_branch = *form->rhs;
  ASSERT_EQ(else_branch.kind, PropertyExpr::Kind::kOr);
  ASSERT_NE(else_branch.lhs, nullptr);
  EXPECT_EQ(else_branch.lhs->kind, PropertyExpr::Kind::kWeak);
  ASSERT_NE(else_branch.lhs->sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*else_branch.lhs->sequence, *Atom("a")));
  EXPECT_EQ(else_branch.rhs, p2);
}

TEST(DerivedConditionalOperators, ClockedFormsAreTheStatedTrees) {
  auto q1 = ClkStrong(Atom("b"));
  auto q2 = ClkStrong(Atom("c"));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkIf(BoolAtom("a"), q1),
                                   *ClkImplication(Atom("a"), q1)));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkIfElse(BoolAtom("a"), q1, q2),
      *ClkAnd(ClkImplication(Atom("a"), q1), ClkOr(ClkWeak(Atom("a")), q2))));
  EXPECT_FALSE(ClockedPropertyEqual(*ClkIfElse(BoolAtom("a"), q1, q2),
                                    *ClkIf(BoolAtom("a"), q1)));
}

TEST(DerivedConditionalOperators, IfRequiresTheBranchOnlyWhereTheBooleanHolds) {
  auto form = PropIf(BoolAtom("a"), PropStrong(Atom("b")));
  const Word kAWithB{A({"a", "b"})};
  const Word kAThenB{A({"a"}), A({"b"})};
  const Word kLoneA{A({"a"})};
  const Word kNoA{A({"x"}), A({"b"})};
  EXPECT_TRUE(NeutrallySatisfies(kAWithB, *form));
  EXPECT_FALSE(NeutrallySatisfies(kAThenB, *form));
  EXPECT_FALSE(NeutrallySatisfies(kLoneA, *form));
  EXPECT_TRUE(NeutrallySatisfies(kNoA, *form));
}

TEST(DerivedConditionalOperators, IfElseRequiresTheBranchTheBooleanSelects) {
  auto with_a_then_b =
      PropIfElse(BoolAtom("a"), PropStrong(Atom("b")), PropStrong(Atom("a")));
  const Word kAWithB{A({"a", "b"})};
  const Word kLoneA{A({"a"})};
  EXPECT_TRUE(NeutrallySatisfies(kAWithB, *with_a_then_b));
  EXPECT_FALSE(NeutrallySatisfies(kLoneA, *with_a_then_b));

  auto else_c =
      PropIfElse(BoolAtom("a"), PropStrong(Atom("b")), PropStrong(Atom("c")));
  const Word kC{A({"c"})};
  const Word kNeither{A({"x"})};
  const Word kB{A({"b"})};
  EXPECT_TRUE(NeutrallySatisfies(kC, *else_c));
  EXPECT_FALSE(NeutrallySatisfies(kNeither, *else_c));
  EXPECT_FALSE(NeutrallySatisfies(kB, *else_c));
}

}  // namespace
