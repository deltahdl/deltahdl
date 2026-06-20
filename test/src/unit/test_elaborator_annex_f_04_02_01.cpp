#include <gtest/gtest.h>

#include "elaborator/checker_rewrite_algorithm.h"

using namespace delta;

namespace {

// §F.4.2.1 main loop: the checker algorithm drains a single kind of instance
// (checker instances). It therefore has exactly one stage, whose successor is
// itself — unlike §F.4.1.1's properties→sequences progression.
TEST(CheckerRewriteAlgorithm, MainLoopHasSingleStage) {
  EXPECT_EQ(FirstCheckerRewriteStage(), CheckerRewriteStage::kCheckerInstances);
  EXPECT_EQ(NextCheckerRewriteStage(CheckerRewriteStage::kCheckerInstances),
            CheckerRewriteStage::kCheckerInstances);
}

// §F.4.2.1 steps 3–5: a formal input argument is rewritten when it is untyped,
// typed non-matching, or typed matching.
TEST(CheckerRewriteAlgorithm, RewritesTheThreeFormalInputKinds) {
  EXPECT_TRUE(CheckerAlgorithmHandlesFormal(FormalKind::kUntyped));
  EXPECT_TRUE(CheckerAlgorithmHandlesFormal(FormalKind::kTypedNonMatching));
  EXPECT_TRUE(CheckerAlgorithmHandlesFormal(FormalKind::kTypedMatching));
}

// §F.4.2.1 step 6: a checker formal input argument is never a local variable,
// so the checker algorithm has no local-variable substitution step (contrast
// §F.4.1.1 step 6) — step 6 only returns the body.
TEST(CheckerRewriteAlgorithm, HasNoLocalVariableFormalStep) {
  EXPECT_FALSE(CheckerAlgorithmHandlesFormal(FormalKind::kLocalVariable));
}

// §F.4.2.1 step 3: an untyped formal bound to `$` or a variable_lvalue
// substitutes the actual unchanged; otherwise it is cast through the actual's
// own type. The checker algorithm reuses §F.4.1.1's substitution decision.
TEST(CheckerRewriteAlgorithm, UntypedFormalSubstitution) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kUntyped,
                                          ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kActualDirect);
  EXPECT_EQ(
      ReplaceCheckerFormalReference(FormalKind::kUntyped, ActualNature::kOther),
      ReferenceReplacement::kItemCastInferredType);
}

// §F.4.2.1 step 4: a typed non-matching formal casts to the formal type t
// directly when t is a casting_type, otherwise through type(t).
TEST(CheckerRewriteAlgorithm, TypedNonMatchingFormalCasts) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedNonMatching,
                                          ActualNature::kCastingType),
            ReferenceReplacement::kItemCastToFormalType);
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedNonMatching,
                                          ActualNature::kOther),
            ReferenceReplacement::kItemCastTypeOfFormal);
}

// §F.4.2.1 step 5: a typed matching formal is item-wrapped when the reference
// is a sequence_method_call operand, and otherwise merely parenthesized.
TEST(CheckerRewriteAlgorithm, TypedMatchingFormalSubstitution) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedMatching,
                                          ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemActual);
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedMatching,
                                          ActualNature::kOther),
            ReferenceReplacement::kParenthesizedActual);
}

// §F.4.2.1 step 4 shall: a reference replaced by a cast in step 4 shall not be
// a variable_lvalue anywhere in the checker. The replacement (a cast) can never
// be an lvalue, and the prohibition spans the whole checker — a wider scope
// than §F.4.1.1's, which is confined to a sequence_match_item assignment
// target.
TEST(CheckerRewriteAlgorithm,
     Step4ReplacementForbidsVariableLvalueWholeChecker) {
  Step4LvalueRule rule = CheckerStep4LvalueRule();
  EXPECT_FALSE(rule.replacement_may_be_lvalue);
  EXPECT_EQ(rule.scope, LvalueProhibitionScope::kWholeChecker);
}

// §F.4.2.1 step 3 (edge): the untyped-formal branch keys only on whether the
// actual is `$`/variable_lvalue. The casting_type and sequence_method_call
// forms — the distinctions steps 4 and 5 draw — do not divert step 3, which
// still casts the actual through its own inferred type.
TEST(CheckerRewriteAlgorithm, UntypedFormalIgnoresOtherStepsActualForms) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kUntyped,
                                          ActualNature::kCastingType),
            ReferenceReplacement::kItemCastInferredType);
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kUntyped,
                                          ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemCastInferredType);
}

// §F.4.2.1 step 4 (edge): the typed-non-matching branch diverts to the direct
// casting_type cast only when the formal's type is a casting_type. A
// sequence_method_call operand (step 5's concern) does not change step 4, which
// still casts through type(t).
TEST(CheckerRewriteAlgorithm, TypedNonMatchingIgnoresMethodOperandForm) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedNonMatching,
                                          ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemCastTypeOfFormal);
}

// §F.4.2.1 step 4 (edge): the typed-non-matching branch is likewise undiverted
// by a `$`/variable_lvalue actual — step 3's distinguishing form, which matters
// only for an untyped formal. Step 4 keys solely on casting_type, so it still
// casts through type(t) here.
TEST(CheckerRewriteAlgorithm, TypedNonMatchingIgnoresDollarOrLvalueForm) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedNonMatching,
                                          ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kItemCastTypeOfFormal);
}

// §F.4.2.1 step 5 (edge): the typed-matching branch item-wraps only when the
// reference is a sequence_method_call operand. A casting_type or
// `$`/variable_lvalue actual — irrelevant to a matching formal — leaves the
// substitution as the parenthesized actual.
TEST(CheckerRewriteAlgorithm, TypedMatchingParenthesizesUnlessMethodOperand) {
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedMatching,
                                          ActualNature::kCastingType),
            ReferenceReplacement::kParenthesizedActual);
  EXPECT_EQ(ReplaceCheckerFormalReference(FormalKind::kTypedMatching,
                                          ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kParenthesizedActual);
}

}  // namespace
