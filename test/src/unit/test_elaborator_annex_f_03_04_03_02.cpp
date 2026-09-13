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

// §F.3.4.3.2 unfolds the two derived Boolean property operators into the
// §F.3.2 not, or and and: (p1 implies p2) is (not p1 or p2), and (p1 iff p2)
// is the and of the implication each way. The cases check that each factory
// builds the tree the identity names, in both property models, and that under
// §F.5.3.1 the trees hold exactly where the identities say: implies fails only
// where p1 holds and p2 does not, and iff fails exactly where the two part.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const PropertyExpr> StrongAtom(const std::string& name) {
  return PropStrong(SeqBoolean(BoolAtom(name)));
}

// The unclocked implies is the or whose first operand is not p1 and whose
// second is p2 itself.
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

// The unclocked iff is the and of (p1 implies p2) and (p2 implies p1), each
// of them the or above with the operands in that order.
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

// The clocked model of §F.5.1.2 builds the same two trees from its own not,
// or and and.
TEST(DerivedBooleanPropertyOperators, ClockedFormsAreTheSameTrees) {
  auto p1 = ClkStrong(SeqBoolean(BoolAtom("a")));
  auto p2 = ClkStrong(SeqBoolean(BoolAtom("b")));
  EXPECT_TRUE(
      ClockedPropertyEqual(*ClkImplies(p1, p2), *ClkOr(ClkNot(p1), p2)));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkIff(p1, p2), *ClkAnd(ClkOr(ClkNot(p1), p2), ClkOr(ClkNot(p2), p1))));
}

// Under §F.5.3.1, strong(a) implies strong(b) fails on the one letter with a
// and without b, and holds on the other three: where a is absent the not
// carries it, and where b is present the or does. A reading of implies as
// p1 or p2 would hold on the letter with a alone and fail on the letter with
// neither.
TEST(DerivedBooleanPropertyOperators, ImpliesFailsOnlyWhereP1HoldsWithoutP2) {
  auto implies = PropImplies(StrongAtom("a"), StrongAtom("b"));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *implies));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"b"})}, *implies));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a", "b"})}, *implies));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({})}, *implies));
}

// The consequent may be temporal: strong(a) implies strong(a ##1 b) holds on
// a then b, fails on a then a letter without b, and holds on a word that
// never starts with a, whatever follows.
TEST(DerivedBooleanPropertyOperators, ImpliesWithATemporalConsequent) {
  auto a_then_b =
      SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
  auto implies = PropImplies(StrongAtom("a"), PropStrong(a_then_b));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a"}), A({"b"})}, *implies));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"}), A({"x"})}, *implies));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *implies));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"x"}), A({"x"})}, *implies));
}

// strong(a) iff strong(b) holds where the letter has both or neither and
// fails where it has one of them, which parts it from and, which needs both,
// and from or, which takes either.
TEST(DerivedBooleanPropertyOperators, IffHoldsExactlyWhereTheOperandsAgree) {
  auto iff = PropIff(StrongAtom("a"), StrongAtom("b"));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"a", "b"})}, *iff));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({})}, *iff));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"a"})}, *iff));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"b"})}, *iff));
}

}  // namespace
