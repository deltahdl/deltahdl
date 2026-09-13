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

// §F.3.4.3.1 reads a sequence written as a property by the statement it
// stands in: strong(R) in a cover property or expect statement, weak(R) in an
// assert property or assume property statement. The cases check which of the
// two §F.3.2 forms each context yields, in both property models, and that the
// two forms part on a word that begins the sequence without completing it,
// which weak(R) accepts and strong(R) does not under §F.5.3.1.

namespace {

Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

std::shared_ptr<const SequenceExpr> AThenB() {
  return SeqConcat(SeqBoolean(BoolAtom("a")), SeqBoolean(BoolAtom("b")));
}

// The cover property and expect statements read the sequence as strong(R); the
// assert property and assume property statements, and the restrict property
// statement that §F.3.4.1 makes an assume, read it as weak(R).
TEST(DerivedSequentialProperty, TheStatementDecidesTheStrength) {
  EXPECT_TRUE(BareSequenceIsStrong(SequencePropertyContext::kCoverProperty));
  EXPECT_TRUE(BareSequenceIsStrong(SequencePropertyContext::kExpect));
  EXPECT_FALSE(BareSequenceIsStrong(SequencePropertyContext::kAssertProperty));
  EXPECT_FALSE(BareSequenceIsStrong(SequencePropertyContext::kAssumeProperty));
  EXPECT_FALSE(
      BareSequenceIsStrong(SequencePropertyContext::kRestrictProperty));
}

// In the unclocked property model the derived property is the strong or the
// weak form over the same sequence.
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

// In the clocked property model of §F.5.1.2 the same reading yields ClkStrong
// or ClkWeak.
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

// The two readings part under §F.5.3.1 on a word that begins a ##1 b and stops
// after a: the assert's weak(R) is satisfied, the cover's strong(R) is not,
// and both are satisfied by a then b and neither by a word that cannot start
// the sequence.
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
