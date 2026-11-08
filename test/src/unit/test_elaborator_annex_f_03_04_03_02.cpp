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

std::shared_ptr<const PropertyExpr> StrongAtom(const std::string& name) {
  return PropStrong(SeqBoolean(BoolAtom(name)));
}

TEST(DerivedBooleanPropertyOperators, UnclockedImpliesIsNotP1OrP2) {
  auto p1 = StrongAtom("a");
  auto p2 = StrongAtom("b");
  auto implies = PropImplies(p1, p2);
  ASSERT_EQ(implies->kind, PropertyExpr::Kind::kOr);
  ASSERT_NE(implies->lhs, nullptr);
  EXPECT_EQ(implies->lhs->kind, PropertyExpr::Kind::kNot);
  EXPECT_EQ(implies->lhs->lhs, p1);
  EXPECT_EQ(implies->rhs, p2);
}

TEST(DerivedBooleanPropertyOperators, UnclockedIffIsTheAndOfBothImplications) {
  auto p1 = StrongAtom("a");
  auto p2 = StrongAtom("b");
  auto iff = PropIff(p1, p2);
  ASSERT_EQ(iff->kind, PropertyExpr::Kind::kAnd);
  auto expect_implies = [](const std::shared_ptr<const PropertyExpr>& tree,
                           const std::shared_ptr<const PropertyExpr>& from,
                           const std::shared_ptr<const PropertyExpr>& to) {
    ASSERT_NE(tree, nullptr);
    EXPECT_EQ(tree->kind, PropertyExpr::Kind::kOr);
    ASSERT_NE(tree->lhs, nullptr);
    EXPECT_EQ(tree->lhs->kind, PropertyExpr::Kind::kNot);
    EXPECT_EQ(tree->lhs->lhs, from);
    EXPECT_EQ(tree->rhs, to);
  };
  expect_implies(iff->lhs, p1, p2);
  expect_implies(iff->rhs, p2, p1);
}

TEST(DerivedBooleanPropertyOperators, ClockedFormsAreTheSameTrees) {
  auto p1 = ClkStrong(SeqBoolean(BoolAtom("a")));
  auto p2 = ClkStrong(SeqBoolean(BoolAtom("b")));
  EXPECT_TRUE(
      ClockedPropertyEqual(*ClkImplies(p1, p2), *ClkOr(ClkNot(p1), p2)));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkIff(p1, p2), *ClkAnd(ClkOr(ClkNot(p1), p2), ClkOr(ClkNot(p2), p1))));
}

TEST(DerivedBooleanPropertyOperators, ImpliesFailsOnlyWhereP1HoldsWithoutP2) {
  auto implies = PropImplies(StrongAtom("a"), StrongAtom("b"));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *implies));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"b"})}, *implies));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a", "b"})}, *implies));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({})}, *implies));
}

TEST(DerivedBooleanPropertyOperators, ImpliesWithATemporalConsequent) {
  auto a_then_b =
      SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  auto implies = PropImplies(StrongAtom("a"), PropStrong(a_then_b));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *implies));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"x"})}, *implies));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *implies));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"}), A({"x"})}, *implies));
}

TEST(DerivedBooleanPropertyOperators, IffHoldsExactlyWhereTheOperandsAgree) {
  auto iff = PropIff(StrongAtom("a"), StrongAtom("b"));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a", "b"})}, *iff));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({})}, *iff));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *iff));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"b"})}, *iff));
}

}  // namespace
