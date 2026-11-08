#include <gtest/gtest.h>

#include <optional>

#include "elaborator/property_rewrite.h"
#include "elaborator/rewrite_algorithm.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(RewriteAlgorithm, PropertiesAreFlattenedBeforeSequences) {
  EXPECT_EQ(FirstRewriteStage(), RewriteStage::kProperties);
  EXPECT_EQ(NextRewriteStage(RewriteStage::kProperties),
            RewriteStage::kSequences);
  EXPECT_EQ(NextRewriteStage(RewriteStage::kSequences),
            RewriteStage::kSequences);
}

TEST(RewriteAlgorithm, SequenceInstanceWrappedInClockAndMethodContexts) {
  EXPECT_TRUE(SequenceInstanceNeedsItemWrap(
      SequenceInstanceContext::kClockingEventOperand));
  EXPECT_TRUE(SequenceInstanceNeedsItemWrap(
      SequenceInstanceContext::kSequenceMethodOperand));
}

TEST(RewriteAlgorithm, OrdinarySequenceInstanceNotWrapped) {
  EXPECT_FALSE(
      SequenceInstanceNeedsItemWrap(SequenceInstanceContext::kOrdinary));
}

TEST(RewriteAlgorithm, ActualIsTheBoundOneElseTheDeclaredDefault) {
  EXPECT_EQ(ActualArgumentFor(true, false),
            ActualArgumentSource::kBoundInInstance);
  EXPECT_EQ(ActualArgumentFor(true, true),
            ActualArgumentSource::kBoundInInstance);
  EXPECT_EQ(ActualArgumentFor(false, true),
            ActualArgumentSource::kDeclaredDefault);
  EXPECT_EQ(ActualArgumentFor(false, false), std::nullopt);
}

TEST(RewriteAlgorithm, UnboundFormalTakesItsDeclaredDefault) {
  PropertyRegistry reg;
  ModuleItem decl;
  decl.kind = ModuleItemKind::kPropertyDecl;
  decl.name = "p";
  decl.prop_formals = {"a", "b", "c"};
  decl.prop_formal_has_default = {false, false, true};
  reg.Register(&decl);

  EXPECT_TRUE(reg.Flatten("p", 2).legal);
  EXPECT_FALSE(reg.Flatten("p", 1).legal);
  EXPECT_TRUE(reg.Flatten("p", 3).legal);
  EXPECT_FALSE(reg.Flatten("p", 4).legal);
}

TEST(RewriteAlgorithm, UntypedFormalSubstitution) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kUntyped,
                                   ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kActualDirect);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kUntyped, ActualNature::kOther),
            ReferenceReplacement::kItemCastInferredType);
}

TEST(RewriteAlgorithm, TypedNonMatchingFormalCasts) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedNonMatching,
                                   ActualNature::kCastingType),
            ReferenceReplacement::kItemCastToFormalType);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedNonMatching,
                                   ActualNature::kOther),
            ReferenceReplacement::kItemCastTypeOfFormal);
}

TEST(RewriteAlgorithm, TypedMatchingFormalSubstitution) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedMatching,
                                   ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemActual);
  EXPECT_EQ(
      ReplaceFormalReference(FormalKind::kTypedMatching, ActualNature::kOther),
      ReferenceReplacement::kParenthesizedActual);
}

TEST(RewriteAlgorithm, UntypedFormalCastIgnoresOtherStepsActualForms) {
  EXPECT_EQ(
      ReplaceFormalReference(FormalKind::kUntyped, ActualNature::kCastingType),
      ReferenceReplacement::kItemCastInferredType);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kUntyped,
                                   ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemCastInferredType);
}

TEST(RewriteAlgorithm, TypedNonMatchingCastIgnoresMethodOperandForm) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedNonMatching,
                                   ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kItemCastTypeOfFormal);
}

TEST(RewriteAlgorithm, TypedMatchingParenthesizesUnlessMethodOperand) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedMatching,
                                   ActualNature::kCastingType),
            ReferenceReplacement::kParenthesizedActual);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kTypedMatching,
                                   ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kParenthesizedActual);
}

TEST(RewriteAlgorithm, LocalVariableReferenceSubstitutesDirectly) {
  EXPECT_EQ(
      ReplaceFormalReference(FormalKind::kLocalVariable, ActualNature::kOther),
      ReferenceReplacement::kActualDirect);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kLocalVariable,
                                   ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kActualDirect);
}

TEST(RewriteAlgorithm, CastsThroughTheFormalTypeMayNotStandAsMatchItemLvalues) {
  EXPECT_FALSE(ReplacementMayStandAsMatchItemLvalue(
      ReferenceReplacement::kItemCastToFormalType));
  EXPECT_FALSE(ReplacementMayStandAsMatchItemLvalue(
      ReferenceReplacement::kItemCastTypeOfFormal));
  EXPECT_TRUE(ReplacementMayStandAsMatchItemLvalue(
      ReferenceReplacement::kActualDirect));
  EXPECT_TRUE(ReplacementMayStandAsMatchItemLvalue(
      ReferenceReplacement::kItemCastInferredType));
  EXPECT_TRUE(
      ReplacementMayStandAsMatchItemLvalue(ReferenceReplacement::kItemActual));
  EXPECT_TRUE(ReplacementMayStandAsMatchItemLvalue(
      ReferenceReplacement::kParenthesizedActual));
}

TEST(RewriteAlgorithm, ParenthesesOmittedOnlyWhereTheReferenceHasThem) {
  EXPECT_FALSE(ParenthesizedActualNeedsParentheses(true));
  EXPECT_TRUE(ParenthesizedActualNeedsParentheses(false));
}

TEST(RewriteAlgorithm, InputLocalVariableDeclaresWithInitializerOnly) {
  auto sub = LocalVariableFlatten(LocalVarDirection::kInput);
  EXPECT_TRUE(sub.declaration_has_initializer);
  EXPECT_FALSE(sub.appends_match_assignment);
}

TEST(RewriteAlgorithm, InoutLocalVariableInitializesAndWritesBack) {
  auto sub = LocalVariableFlatten(LocalVarDirection::kInout);
  EXPECT_TRUE(sub.declaration_has_initializer);
  EXPECT_TRUE(sub.appends_match_assignment);
}

TEST(RewriteAlgorithm, OutputLocalVariableWritesBackWithoutInitializer) {
  auto sub = LocalVariableFlatten(LocalVarDirection::kOutput);
  EXPECT_FALSE(sub.declaration_has_initializer);
  EXPECT_TRUE(sub.appends_match_assignment);
}

TEST(RewriteAlgorithm, PropertyLocalVariableDeclaresWithInitializerOnly) {
  auto sub = PropertyLocalVariableFlatten();
  EXPECT_TRUE(sub.declaration_has_initializer);
  EXPECT_FALSE(sub.appends_match_assignment);
}

TEST(RewriteAlgorithm, FlattenedFormsAreParenthesizedAndOrderFree) {
  auto property = FlattenedForm(FlattenTarget::kProperty);
  EXPECT_FALSE(property.local_var_declarations_ordered);
  EXPECT_FALSE(property.appends_match_item_assignments);
  EXPECT_FALSE(property.match_item_assignments_ordered);
  EXPECT_TRUE(property.enclosed_in_parentheses);
  auto sequence = FlattenedForm(FlattenTarget::kSequence);
  EXPECT_FALSE(sequence.local_var_declarations_ordered);
  EXPECT_TRUE(sequence.appends_match_item_assignments);
  EXPECT_FALSE(sequence.match_item_assignments_ordered);
  EXPECT_TRUE(sequence.enclosed_in_parentheses);
}

}  // namespace
