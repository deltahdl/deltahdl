#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

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

std::shared_ptr<const BooleanExpr> Eq(
    const std::shared_ptr<const BooleanExpr>&,
    const std::shared_ptr<const BooleanExpr>& item) {
  return BoolAtom("eq_" + item->atom);
}

TEST(DerivedCaseOperators, ADefaultAloneIsTheDefault) {
  auto pd = PropStrong(Atom("d"));
  EXPECT_EQ(PropCase(BoolAtom("sel"), {}, pd, Eq), pd);
  EXPECT_EQ(PropCase(BoolAtom("sel"), {}, nullptr, Eq), nullptr);
  auto qd = ClkStrong(Atom("d"));
  EXPECT_EQ(ClkCase(BoolAtom("sel"), {}, qd, Eq), qd);
  EXPECT_EQ(ClkCase(BoolAtom("sel"), {}, nullptr, Eq), nullptr);
}

TEST(DerivedCaseOperators, OneItemWithoutADefaultIsTheConditional) {
  auto p1 = PropStrong(Atom("a"));
  auto form = PropCase(BoolAtom("sel"), {{BoolAtom("x"), p1}}, nullptr, Eq);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(form->sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*form->sequence, *Atom("eq_x")));
  EXPECT_EQ(form->lhs, p1);
}

TEST(DerivedCaseOperators, OneItemWithADefaultIsTheConditionalWithAnElse) {
  auto p1 = PropStrong(Atom("a"));
  auto pd = PropStrong(Atom("d"));
  auto form = PropCase(BoolAtom("sel"), {{BoolAtom("x"), p1}}, pd, Eq);
  ASSERT_EQ(form->kind, PropertyExpr::Kind::kAnd);
  ASSERT_NE(form->lhs, nullptr);
  ASSERT_NE(form->rhs, nullptr);
  ASSERT_EQ(form->lhs->kind, PropertyExpr::Kind::kImplication);
  ASSERT_NE(form->lhs->sequence, nullptr);
  EXPECT_TRUE(SequenceExprEqual(*form->lhs->sequence, *Atom("eq_x")));
  EXPECT_EQ(form->lhs->lhs, p1);
  ASSERT_EQ(form->rhs->kind, PropertyExpr::Kind::kOr);
  ASSERT_NE(form->rhs->lhs, nullptr);
  EXPECT_EQ(form->rhs->lhs->kind, PropertyExpr::Kind::kWeak);
  EXPECT_EQ(form->rhs->rhs, pd);
}

TEST(DerivedCaseOperators, MoreItemsNestTheCaseOverTheRestAsTheElse) {
  auto p1 = PropStrong(Atom("a"));
  auto p2 = PropStrong(Atom("b"));
  auto pd = PropStrong(Atom("d"));
  const std::vector<PropCaseItem> kItems{{BoolAtom("x"), p1},
                                         {BoolAtom("y"), p2}};
  auto without = PropCase(BoolAtom("sel"), kItems, nullptr, Eq);
  ASSERT_EQ(without->kind, PropertyExpr::Kind::kAnd);
  EXPECT_TRUE(SequenceExprEqual(*without->lhs->sequence, *Atom("eq_x")));
  EXPECT_EQ(without->lhs->lhs, p1);
  const PropertyExpr& second = *without->rhs->rhs;
  ASSERT_EQ(second.kind, PropertyExpr::Kind::kImplication);
  EXPECT_TRUE(SequenceExprEqual(*second.sequence, *Atom("eq_y")));
  EXPECT_EQ(second.lhs, p2);

  auto with = PropCase(BoolAtom("sel"), kItems, pd, Eq);
  ASSERT_EQ(with->kind, PropertyExpr::Kind::kAnd);
  EXPECT_EQ(with->lhs->lhs, p1);
  const PropertyExpr& second_with_else = *with->rhs->rhs;
  ASSERT_EQ(second_with_else.kind, PropertyExpr::Kind::kAnd);
  EXPECT_TRUE(
      SequenceExprEqual(*second_with_else.lhs->sequence, *Atom("eq_y")));
  EXPECT_EQ(second_with_else.lhs->lhs, p2);
  EXPECT_EQ(second_with_else.rhs->rhs, pd);
}

TEST(DerivedCaseOperators, TheMatchIsAskedAboutTheCaseExpressionPerItem) {
  auto sel = BoolAtom("sel");
  std::vector<std::shared_ptr<const BooleanExpr>> asked_about;
  const CaseMatch kRecordingEq =
      [&asked_about](const std::shared_ptr<const BooleanExpr>& b,
                     const std::shared_ptr<const BooleanExpr>& item) {
        asked_about.push_back(b);
        return Eq(b, item);
      };
  PropCase(sel, {}, PropStrong(Atom("d")), kRecordingEq);
  EXPECT_TRUE(asked_about.empty());
  PropCase(sel,
           {{BoolAtom("x"), PropStrong(Atom("a"))},
            {BoolAtom("y"), PropStrong(Atom("b"))}},
           nullptr, kRecordingEq);
  ASSERT_EQ(asked_about.size(), 2U);
  EXPECT_EQ(asked_about[0], sel);
  EXPECT_EQ(asked_about[1], sel);
  asked_about.clear();
  ClkCase(sel, {{BoolAtom("x"), ClkStrong(Atom("a"))}}, nullptr, kRecordingEq);
  ASSERT_EQ(asked_about.size(), 1U);
  EXPECT_EQ(asked_about[0], sel);
}

TEST(DerivedCaseOperators, ClockedFormsAreTheStatedTrees) {
  auto q1 = ClkStrong(Atom("a"));
  auto q2 = ClkStrong(Atom("b"));
  auto qd = ClkStrong(Atom("d"));
  auto sel = BoolAtom("sel");
  EXPECT_TRUE(
      ClockedPropertyEqual(*ClkCase(sel, {{BoolAtom("x"), q1}}, nullptr, Eq),
                           *ClkIf(BoolAtom("eq_x"), q1)));
  EXPECT_TRUE(ClockedPropertyEqual(*ClkCase(sel, {{BoolAtom("x"), q1}}, qd, Eq),
                                   *ClkIfElse(BoolAtom("eq_x"), q1, qd)));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkCase(sel, {{BoolAtom("x"), q1}, {BoolAtom("y"), q2}}, qd, Eq),
      *ClkIfElse(BoolAtom("eq_x"), q1, ClkIfElse(BoolAtom("eq_y"), q2, qd))));
  EXPECT_FALSE(ClockedPropertyEqual(
      *ClkCase(sel, {{BoolAtom("x"), q1}, {BoolAtom("y"), q2}}, qd, Eq),
      *ClkIfElse(BoolAtom("eq_x"), q1, ClkIf(BoolAtom("eq_y"), q2))));
}

TEST(DerivedCaseOperators, TheFirstMatchingItemDecidesTheVerdict) {
  const std::vector<PropCaseItem> kItems{
      {BoolAtom("x"), PropStrong(Atom("a"))},
      {BoolAtom("y"), PropStrong(Atom("b"))}};
  auto with_default =
      PropCase(BoolAtom("sel"), kItems, PropStrong(Atom("c")), Eq);
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"eq_x", "a"})}, *with_default));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"eq_x", "b"})}, *with_default));
  EXPECT_FALSE(
      NeutrallySatisfies(Word{A({"eq_x", "eq_y", "b"})}, *with_default));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"eq_y", "b"})}, *with_default));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"eq_y", "a"})}, *with_default));
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"c"})}, *with_default));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"z"})}, *with_default));

  auto without_default = PropCase(BoolAtom("sel"), kItems, nullptr, Eq);
  EXPECT_TRUE(NeutrallySatisfies(Word{A({"z"})}, *without_default));
  EXPECT_FALSE(NeutrallySatisfies(Word{A({"eq_y", "a"})}, *without_default));
}

}  // namespace
