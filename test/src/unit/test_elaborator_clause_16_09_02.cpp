#include <gtest/gtest.h>

#include "elaborator/sequence_repetition.h"

using namespace delta;

namespace {

TEST(RepetitionCount, ExactCountIsAlwaysWellFormed) {
  // §16.9.2: an exact count is given by a single non-negative integer
  // constant expression and is well-formed by itself.
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeExactCount(0)));
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeExactCount(3)));
}

TEST(RepetitionCount, FiniteRangeRequiresMinNoGreaterThanMax) {
  // §16.9.2: if both min and max are defined by non-negative integer
  // constant expressions, min ≤ max.
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeFiniteRange(2, 5)));
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeFiniteRange(3, 3)));
  EXPECT_FALSE(IsRepetitionCountWellFormed(MakeFiniteRange(5, 2)));
}

TEST(RepetitionCount, DollarRangeIsWellFormed) {
  // §16.9.2: the maximum may be the dollar sign, indicating finite but
  // unbounded.
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeDollarRange(0)));
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeDollarRange(10)));
}

TEST(RepetitionShortcuts, StarAndPlusExpandToDollarRanges) {
  // §16.9.2: [*] ≡ [*0:$] and [+] ≡ [*1:$].
  auto star = NormalizeStarShortcut();
  EXPECT_TRUE(star.max_is_dollar);
  EXPECT_EQ(star.min, 0u);

  auto plus = NormalizePlusShortcut();
  EXPECT_TRUE(plus.max_is_dollar);
  EXPECT_EQ(plus.min, 1u);
}

TEST(RepetitionContext, ConsecutiveAllowedOnSequenceAndBoolean) {
  // §16.9.2: the consecutive repetition operator applies to general
  // sequence expressions, Boolean operands included.
  EXPECT_TRUE(IsRepetitionAllowedOn(RepetitionKind::kConsecutive,
                                    /*operand_is_boolean_expr=*/true,
                                    /*boolean_has_attached_match_item=*/false));
  EXPECT_TRUE(IsRepetitionAllowedOn(RepetitionKind::kConsecutive,
                                    /*operand_is_boolean_expr=*/false,
                                    /*boolean_has_attached_match_item=*/false));
}

TEST(RepetitionContext, GotoAndNonconsecutiveRequireBareBoolean) {
  // §16.9.2: goto and nonconsecutive repetition operate only on Boolean
  // expressions, and not on a Boolean to which a sequence_match_item (see
  // §16.10/§16.11) has been attached.
  EXPECT_FALSE(
      IsRepetitionAllowedOn(RepetitionKind::kGoto,
                            /*operand_is_boolean_expr=*/false,
                            /*boolean_has_attached_match_item=*/false));
  EXPECT_TRUE(IsRepetitionAllowedOn(RepetitionKind::kGoto,
                                    /*operand_is_boolean_expr=*/true,
                                    /*boolean_has_attached_match_item=*/false));
  EXPECT_FALSE(IsRepetitionAllowedOn(RepetitionKind::kGoto,
                                     /*operand_is_boolean_expr=*/true,
                                     /*boolean_has_attached_match_item=*/true));
  EXPECT_FALSE(IsRepetitionAllowedOn(RepetitionKind::kNonconsecutive,
                                     /*operand_is_boolean_expr=*/true,
                                     /*boolean_has_attached_match_item=*/true));
}

TEST(RepetitionContext, NonconsecutiveRequiresBareBoolean) {
  // §16.9.2: the Boolean-only restriction applies to nonconsecutive
  // repetition exactly as it does to goto repetition. A non-Boolean operand
  // is rejected; a bare Boolean operand is accepted.
  EXPECT_FALSE(
      IsRepetitionAllowedOn(RepetitionKind::kNonconsecutive,
                            /*operand_is_boolean_expr=*/false,
                            /*boolean_has_attached_match_item=*/false));
  EXPECT_TRUE(IsRepetitionAllowedOn(RepetitionKind::kNonconsecutive,
                                    /*operand_is_boolean_expr=*/true,
                                    /*boolean_has_attached_match_item=*/false));
}

TEST(RepetitionZero, OnlyConsecutivePermitsZeroIterations) {
  // §16.9.2 (and the anchor for §16.9.2.1): only consecutive repetition
  // has a defined zero-iteration semantics. Goto/nonconsecutive require a
  // matching iteration of the Boolean operand and therefore cannot run
  // with zero iterations.
  EXPECT_TRUE(IsZeroRepetitionPermitted(RepetitionKind::kConsecutive));
  EXPECT_FALSE(IsZeroRepetitionPermitted(RepetitionKind::kGoto));
  EXPECT_FALSE(IsZeroRepetitionPermitted(RepetitionKind::kNonconsecutive));
}

}  // namespace
