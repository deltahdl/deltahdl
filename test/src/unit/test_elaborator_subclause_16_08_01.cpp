#include <gtest/gtest.h>

#include "elaborator/typed_sequence_formal.h"

using namespace delta;

namespace {

TEST(TypedSequenceFormal, AllowedTypeKindsIncludeUntypedSequenceEventIntegral) {
  // §16.8.1: a formal argument's type may be `untyped`, `sequence`, `event`,
  // or one of the types allowed in §16.6.
  EXPECT_TRUE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kUntyped));
  EXPECT_TRUE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kSequence));
  EXPECT_TRUE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kEvent));
  EXPECT_TRUE(
      IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kIntegralOrUserType));
}

TEST(TypedSequenceFormal, ForbiddenTypeKindRejected) {
  // §16.8.1: anything outside the allowed list is not a valid sequence
  // formal type.
  EXPECT_FALSE(IsSequenceFormalTypeAllowed(SequenceFormalTypeKind::kForbidden));
}

TEST(TypedSequenceFormal, SequenceTypedRefLegalPlaces) {
  // §16.8.1(a): a reference to a `sequence`-typed formal shall stand in a
  // sequence_expr place, or as the operand of `triggered`/`matched`.
  EXPECT_TRUE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kSequenceExprPosition));
  EXPECT_TRUE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kTriggeredMethodOperand));
  EXPECT_TRUE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kMatchedMethodOperand));
  EXPECT_FALSE(IsSequenceTypedFormalRefLegal(
      SequenceTypedFormalRefPlace::kOtherPosition));
}

TEST(TypedSequenceFormal, EventTypedRefRequiresEventExpressionPosition) {
  // §16.8.1(b): a reference to an `event`-typed formal shall be in a place
  // where an event_expression may be written.
  EXPECT_TRUE(
      IsEventTypedFormalRefLegal(/*in_event_expression_position=*/true));
  EXPECT_FALSE(
      IsEventTypedFormalRefLegal(/*in_event_expression_position=*/false));
}

TEST(TypedSequenceFormal, SequenceTypedFormalForbiddenAsGotoOperand) {
  // §16.8.1 (cross-link to §16.9.2): a sequence-typed formal may not be the
  // expression_or_dist operand of a goto_repetition.
  EXPECT_FALSE(IsSequenceTypedFormalAllowedAsGotoOperand());
}

TEST(TypedSequenceFormal, TypedFormalLvalueInMatchItemOnlyForLocalVar) {
  // §16.8.1 (cross-link to §16.11/§16.10): a typed formal reference inside
  // a sequence_match_item shall not stand as the variable_lvalue in an
  // operator_assignment or inc_or_dec_expression — unless the formal is a
  // local variable formal.
  EXPECT_FALSE(IsTypedFormalAllowedAsMatchItemLvalue(
      /*is_local_var_formal=*/false));
  EXPECT_TRUE(IsTypedFormalAllowedAsMatchItemLvalue(
      /*is_local_var_formal=*/true));
}

TEST(TypedSequenceFormal, DelayAndRepetitionIndexTypeRestricted) {
  // §16.8.1: a typed formal referenced inside a cycle_delay_range, a
  // boolean_abbrev, or a sequence_abbrev (terms from §16.9.2) shall be of
  // type shortint, int, or longint.
  EXPECT_TRUE(IsDelayOrRepetitionIndexTypeAllowed(
      SequenceFormalIntegralType::kShortint));
  EXPECT_TRUE(
      IsDelayOrRepetitionIndexTypeAllowed(SequenceFormalIntegralType::kInt));
  EXPECT_TRUE(IsDelayOrRepetitionIndexTypeAllowed(
      SequenceFormalIntegralType::kLongint));
  EXPECT_FALSE(IsDelayOrRepetitionIndexTypeAllowed(
      SequenceFormalIntegralType::kOtherIntegral));
}

TEST(TypedSequenceFormal, SubstitutionModePicksLvalueVsCast) {
  // §16.8.1(c): if the actual is a variable_lvalue, mutate-and-assign-back
  // semantics apply. Otherwise the actual is cast to the formal's type
  // before substitution in the §F.4.1 rewriting algorithm.
  EXPECT_EQ(TypedFormalSubstitution(/*actual_is_variable_lvalue=*/true),
            TypedFormalSubstitutionMode::kAssignBackAfterUpdate);
  EXPECT_EQ(TypedFormalSubstitution(/*actual_is_variable_lvalue=*/false),
            TypedFormalSubstitutionMode::kCastBeforeSubstitution);
}

TEST(TypedSequenceFormal, UntypedKeywordRequiredAfterTypedFormal) {
  // §16.8.1: an untyped formal that follows a typed formal in the list must
  // spell `untyped` explicitly, since a bare name would otherwise inherit
  // the preceding data type.
  EXPECT_TRUE(IsUntypedKeywordRequired(/*prev_formal_in_list_was_typed=*/true,
                                       /*this_formal_intended_untyped=*/true));
  EXPECT_FALSE(IsUntypedKeywordRequired(
      /*prev_formal_in_list_was_typed=*/false,
      /*this_formal_intended_untyped=*/true));
  EXPECT_FALSE(IsUntypedKeywordRequired(
      /*prev_formal_in_list_was_typed=*/true,
      /*this_formal_intended_untyped=*/false));
}

TEST(TypedSequenceFormal, EventTypedFormalRejectsEdgeIdentifierActual) {
  // §16.8.1: a formal typed `event` may not receive an actual that will be
  // combined with an edge_identifier to build an event_expression.
  EXPECT_FALSE(IsEventTypedFormalCompatibleWithEdgeIdentifierUse(
      /*formal_typed_event=*/true,
      /*actual_combined_with_edge_identifier=*/true));
  EXPECT_TRUE(IsEventTypedFormalCompatibleWithEdgeIdentifierUse(
      /*formal_typed_event=*/true,
      /*actual_combined_with_edge_identifier=*/false));
  EXPECT_TRUE(IsEventTypedFormalCompatibleWithEdgeIdentifierUse(
      /*formal_typed_event=*/false,
      /*actual_combined_with_edge_identifier=*/true));
}

}  // namespace
