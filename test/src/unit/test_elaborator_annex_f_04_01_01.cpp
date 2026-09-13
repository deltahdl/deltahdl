#include <gtest/gtest.h>

#include <optional>

#include "elaborator/property_rewrite.h"
#include "elaborator/rewrite_algorithm.h"
#include "parser/ast_module.h"

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

// §F.4.1.1 flatten_property/flatten_sequence step 2: a formal bound in the
// instance takes the bound actual, with or without a declared default; one
// not bound takes the declared default; and one neither bound nor defaulted
// has no actual for the algorithm to substitute.
TEST(RewriteAlgorithm, ActualIsTheBoundOneElseTheDeclaredDefault) {
  EXPECT_EQ(ActualArgumentFor(true, false),
            ActualArgumentSource::kBoundInInstance);
  EXPECT_EQ(ActualArgumentFor(true, true),
            ActualArgumentSource::kBoundInInstance);
  EXPECT_EQ(ActualArgumentFor(false, true),
            ActualArgumentSource::kDeclaredDefault);
  EXPECT_EQ(ActualArgumentFor(false, false), std::nullopt);
}

// §F.4.1.1 step 2 on a registered property: with formals a, b and c of
// which c alone declares a default, an instance binding a and b flattens
// legally, since c takes its default, where one binding a alone leaves b
// without an actual, one binding all three is legal, and one binding four
// exceeds the formals.
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

// §F.4.1.1 flatten_property/flatten_sequence step 3: an untyped formal bound
// to `$` or a variable_lvalue substitutes the actual unchanged; bound to any
// other actual it is cast through the actual's own type.
TEST(RewriteAlgorithm, UntypedFormalSubstitution) {
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kUntyped,
                                   ActualNature::kDollarOrLvalue),
            ReferenceReplacement::kActualDirect);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kUntyped, ActualNature::kOther),
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
  EXPECT_EQ(
      ReplaceFormalReference(FormalKind::kTypedMatching, ActualNature::kOther),
      ReferenceReplacement::kParenthesizedActual);
}

// §F.4.1.1 step 3 (edge): the untyped formal's only special case is a `$` or
// variable_lvalue actual. A casting_type actual or a sequence_method_call
// operand — distinctions that belong to steps 4 and 5 — do not divert step 3,
// which still casts through the actual's own type.
TEST(RewriteAlgorithm, UntypedFormalCastIgnoresOtherStepsActualForms) {
  EXPECT_EQ(
      ReplaceFormalReference(FormalKind::kUntyped, ActualNature::kCastingType),
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
  EXPECT_EQ(
      ReplaceFormalReference(FormalKind::kLocalVariable, ActualNature::kOther),
      ReferenceReplacement::kActualDirect);
  EXPECT_EQ(ReplaceFormalReference(FormalKind::kLocalVariable,
                                   ActualNature::kSequenceMethodOperand),
            ReferenceReplacement::kActualDirect);
}

// §F.4.1.1 step 4, by way of §16.8.1: a reference replaced by a cast through
// the formal's type, in either of step 4's two shapes, may not stand as the
// variable_lvalue of an operator_assignment or inc_or_dec_expression in a
// sequence_match_item, where the replacements of steps 3 and 5 may.
TEST(RewriteAlgorithm, Step4CastsMayNotStandAsMatchItemLvalues) {
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

// §F.4.1.1 step 5b: the parentheses around the substituted actual may be
// omitted where the reference is already enclosed in parentheses, and not
// otherwise.
TEST(RewriteAlgorithm, ParenthesesOmittedOnlyWhereTheReferenceHasThem) {
  EXPECT_FALSE(ParenthesizedActualNeedsParentheses(true));
  EXPECT_TRUE(ParenthesizedActualNeedsParentheses(false));
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

// §F.4.1.1 flatten_property step 6: every local variable formal of a
// property becomes a prepended "t f = a_f;" with nothing appended, the shape
// flatten_sequence gives an input and not the shape it gives an output.
TEST(RewriteAlgorithm, PropertyLocalVariableDeclaresWithInitializerOnly) {
  auto sub = PropertyLocalVariableFlatten();
  EXPECT_TRUE(sub.declaration_has_initializer);
  EXPECT_FALSE(sub.appends_match_assignment);
}

// §F.4.1.1 steps 6 and 7 and the closing note: both flatten_property and
// flatten_sequence prepend their local variable declarations in any order
// and enclose the result in parentheses; only flatten_sequence appends
// match-item assignments, and their order does not matter either.
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
