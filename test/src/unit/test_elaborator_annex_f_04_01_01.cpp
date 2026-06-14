#include <gtest/gtest.h>

#include "elaborator/rewrite_algorithm.h"

using namespace delta;

namespace {

// §F.4.1.1 main loop: property instances are flattened first, then sequence
// instances. The fixed order is observable as properties→sequences with
// sequences last.
TEST(RewriteAlgorithm, PropertiesAreFlattenedBeforeSequences) {
  EXPECT_EQ(FirstRewriteStage(), RewriteStage::kProperties);
  EXPECT_EQ(NextRewriteStage(RewriteStage::kProperties),
            RewriteStage::kSequences);
  // Sequences is the terminal stage.
  EXPECT_EQ(NextRewriteStage(RewriteStage::kSequences),
            RewriteStage::kSequences);
}

// §F.4.1.1 main-loop step 2: a sequence instance used as a clocking_event
// operand or as a sequence_method_call operand is wrapped with
// item(sequence'flatten_sequence(r)).
TEST(RewriteAlgorithm, SequenceInstanceWrappedInClockAndMethodContexts) {
  EXPECT_TRUE(SequenceInstanceNeedsItemWrap(
      SequenceInstanceContext::kClockingEventOperand));
  EXPECT_TRUE(SequenceInstanceNeedsItemWrap(
      SequenceInstanceContext::kSequenceMethodOperand));
}

// §F.4.1.1 main-loop step 3: every other sequence-instance occurrence takes
// the bare flatten_sequence(r) with no item wrap.
TEST(RewriteAlgorithm, OrdinarySequenceInstanceNotWrapped) {
  EXPECT_FALSE(
      SequenceInstanceNeedsItemWrap(SequenceInstanceContext::kOrdinary));
}

// §F.4.1.1 flatten_property/flatten_sequence step 3: an untyped formal bound
// to `$` or a variable_lvalue substitutes the actual unchanged; bound to any
// other actual it is cast through the actual's own type.
TEST(RewriteAlgorithm, UntypedFormalSubstitution) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kUntyped,
                                   ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kActualDirect);
  EXPECT_EQ(
      ReplaceFormalReference(FormalKind::kUntyped, ActualNature::kOther),
      ReferenceReplacement::kItemCastInferredType);
}

// §F.4.1.1 step 4: a typed, non-matching formal casts to the formal type t
// directly when t is a casting_type, otherwise through type(t).
TEST(RewriteAlgorithm, TypedNonMatchingFormalCasts) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedNonMatching,
                                   ActualNature::kCastingType),
            ReferenceReplacement::kItemCastToFormalType);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedNonMatching,
                                   ActualNature::kOther),
            ReferenceReplacement::kItemCastTypeOfFormal);
}

// §F.4.1.1 step 5: a typed formal whose type matches event/sequence/property
// is item-wrapped when the reference is a sequence_method_call operand, and
// otherwise merely parenthesized.
TEST(RewriteAlgorithm, TypedMatchingFormalSubstitution) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedMatching,
                                   ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemActual);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedMatching,
                                   ActualNature::kOther),
            ReferenceReplacement::kParenthesizedActual);
}

// §F.4.1.1 step 3 (edge): the untyped formal's only special case is a `$` or
// variable_lvalue actual. A casting_type actual or a sequence_method_call
// operand — distinctions that belong to steps 4 and 5 — do not divert step 3,
// which still casts through the actual's own type.
TEST(RewriteAlgorithm, UntypedFormalCastIgnoresOtherStepsActualForms) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kUntyped,
                                   ActualNature::kCastingType),
            ReferenceReplacement::kItemCastInferredType);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kUntyped,
                                   ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemCastInferredType);
}

// §F.4.1.1 step 4 (edge): a typed non-matching formal diverts to the direct
// cast only when its type is a casting_type. A sequence_method_call operand
// (step 5's concern) does not change step 4, which still casts through
// type(t).
TEST(RewriteAlgorithm, TypedNonMatchingCastIgnoresMethodOperandForm) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedNonMatching,
                                   ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemCastTypeOfFormal);
}

// §F.4.1.1 step 5 (edge): a typed matching formal is item-wrapped only when
// the reference is a sequence_method_call operand. Casting-type or
// $/variable_lvalue actuals — irrelevant to a matching formal — leave the
// substitution as the parenthesized actual.
TEST(RewriteAlgorithm, TypedMatchingParenthesizesUnlessMethodOperand) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedMatching,
                                   ActualNature::kCastingType),
            ReferenceReplacement::kParenthesizedActual);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedMatching,
                                   ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kParenthesizedActual);
}

// §F.4.1.1 step 6: a local variable formal is substituted through prepended
// declarations (see LocalVariableFlatten), so the in-place reference to it
// resolves to the local name directly rather than to any item/cast wrapper,
// regardless of the actual's form.
TEST(RewriteAlgorithm, LocalVariableReferenceSubstitutesDirectly) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kLocalVariable,
                                   ActualNature::kOther),
            ReferenceReplacement::kActualDirect);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kLocalVariable,
                                   ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kActualDirect);
}

// §F.4.1.1 flatten_sequence step 6a: an input local variable formal becomes a
// prepended "t f = a_f;" with no value flowing back out.
TEST(RewriteAlgorithm, InputLocalVariableDeclaresWithInitializerOnly) {
  auto sub = LocalVariableFlatten(LocalVarDirection::kInput);
  EXPECT_TRUE(sub.declaration_has_initializer);
  EXPECT_FALSE(sub.appends_match_assignment);
}

// §F.4.1.1 flatten_sequence step 6b: an inout local variable is initialized
// and also writes back through an appended match-item assignment.
TEST(RewriteAlgorithm, InoutLocalVariableInitializesAndWritesBack) {
  auto sub = LocalVariableFlatten(LocalVarDirection::kInout);
  EXPECT_TRUE(sub.declaration_has_initializer);
  EXPECT_TRUE(sub.appends_match_assignment);
}

// §F.4.1.1 flatten_sequence step 6c: an output local variable is declared
// without an initializer and writes back through the appended assignment.
TEST(RewriteAlgorithm, OutputLocalVariableWritesBackWithoutInitializer) {
  auto sub = LocalVariableFlatten(LocalVarDirection::kOutput);
  EXPECT_FALSE(sub.declaration_has_initializer);
  EXPECT_TRUE(sub.appends_match_assignment);
}

}  // namespace
