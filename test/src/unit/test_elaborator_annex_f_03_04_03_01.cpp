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

std::shared_ptr<const SequenceExpr> AThenB() {
  return SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
}

TEST(DerivedSequentialProperty, TheStatementDecidesTheStrength) {
  EXPECT_TRUE(BareSequenceIsStrong(SequencePropertyContext::kCoverProperty));
  EXPECT_TRUE(BareSequenceIsStrong(SequencePropertyContext::kExpect));
  EXPECT_FALSE(BareSequenceIsStrong(SequencePropertyContext::kAssertProperty));
  EXPECT_FALSE(BareSequenceIsStrong(SequencePropertyContext::kAssumeProperty));
  EXPECT_FALSE(
      BareSequenceIsStrong(SequencePropertyContext::kRestrictProperty));
}

TEST(DerivedSequentialProperty, UnclockedFormIsStrongOrWeakOfTheSequence) {
  auto r = AThenB();
  auto expect_form = [&](SequencePropertyContext context,
                         PropertyExpr::Kind kind) {
    auto p = PropOfBareSequence(r, context);
    EXPECT_EQ(p->kind, kind);
    ASSERT_NE(p->sequence, nullptr);
    EXPECT_TRUE(SequenceExprEqual(*p->sequence, *r));
  };
  expect_form(SequencePropertyContext::kCoverProperty,
              PropertyExpr::Kind::kStrong);
  expect_form(SequencePropertyContext::kExpect, PropertyExpr::Kind::kStrong);
  expect_form(SequencePropertyContext::kAssertProperty,
              PropertyExpr::Kind::kWeak);
  expect_form(SequencePropertyContext::kAssumeProperty,
              PropertyExpr::Kind::kWeak);
  expect_form(SequencePropertyContext::kRestrictProperty,
              PropertyExpr::Kind::kWeak);
}

TEST(DerivedSequentialProperty, ClockedFormIsStrongOrWeakOfTheSequence) {
  auto r = AThenB();
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkOfBareSequence(r, SequencePropertyContext::kCoverProperty),
      *ClkStrong(r)));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkOfBareSequence(r, SequencePropertyContext::kExpect), *ClkStrong(r)));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkOfBareSequence(r, SequencePropertyContext::kAssertProperty),
      *ClkWeak(r)));
  EXPECT_TRUE(ClockedPropertyEqual(
      *ClkOfBareSequence(r, SequencePropertyContext::kAssumeProperty),
      *ClkWeak(r)));
}

TEST(DerivedSequentialProperty, TheTwoReadingsPartOnAnUnfinishedWord) {
  auto in_assert =
      PropOfBareSequence(AThenB(), SequencePropertyContext::kAssertProperty);
  auto in_cover =
      PropOfBareSequence(AThenB(), SequencePropertyContext::kCoverProperty);
  const Word kUnfinished{A({"a"})};
  const Word kComplete{A({"a"}), A({"b"})};
  const Word kWrong{A({"x"})};
  EXPECT_TRUE(NeutrallySatisfies(kUnfinished, *in_assert));
  EXPECT_FALSE(NeutrallySatisfies(kUnfinished, *in_cover));
  EXPECT_TRUE(NeutrallySatisfies(kComplete, *in_assert));
  EXPECT_TRUE(NeutrallySatisfies(kComplete, *in_cover));
  EXPECT_FALSE(NeutrallySatisfies(kWrong, *in_assert));
  EXPECT_FALSE(NeutrallySatisfies(kWrong, *in_cover));
}

}  // namespace
