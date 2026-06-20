#include "elaborator/typed_sequence_formal.h"

namespace delta {

bool IsSequenceFormalTypeAllowed(SequenceFormalTypeKind kind) {
  switch (kind) {
    case SequenceFormalTypeKind::kUntyped:
    case SequenceFormalTypeKind::kSequence:
    case SequenceFormalTypeKind::kEvent:
    case SequenceFormalTypeKind::kIntegralOrUserType:
      return true;
    case SequenceFormalTypeKind::kForbidden:
      return false;
  }
  return false;
}

bool IsSequenceTypedFormalRefLegal(SequenceTypedFormalRefPlace where) {
  switch (where) {
    case SequenceTypedFormalRefPlace::kSequenceExprPosition:
    case SequenceTypedFormalRefPlace::kTriggeredMethodOperand:
    case SequenceTypedFormalRefPlace::kMatchedMethodOperand:
      return true;
    case SequenceTypedFormalRefPlace::kOtherPosition:
      return false;
  }
  return false;
}

bool IsEventTypedFormalRefLegal(bool in_event_expression_position) {
  return in_event_expression_position;
}

bool IsSequenceTypedFormalAllowedAsGotoOperand() {
  // §16.8.1: a sequence-typed formal may not be the expression_or_dist
  // operand of a goto_repetition. §16.9.2 lays out the same restriction
  // from the goto side (goto/nonconsecutive repetition applies only to
  // Boolean expressions, never to sequence_exprs).
  return false;
}

bool IsTypedFormalAllowedAsMatchItemLvalue(bool is_local_var_formal) {
  // §16.8.1: outside the local-variable carve-out, a typed formal reference
  // cannot stand as the variable_lvalue in an operator_assignment or
  // inc_or_dec_expression that lives inside a sequence_match_item.
  return is_local_var_formal;
}

bool IsDelayOrRepetitionIndexTypeAllowed(SequenceFormalIntegralType t) {
  switch (t) {
    case SequenceFormalIntegralType::kShortint:
    case SequenceFormalIntegralType::kInt:
    case SequenceFormalIntegralType::kLongint:
      return true;
    case SequenceFormalIntegralType::kOtherIntegral:
      return false;
  }
  return false;
}

TypedFormalSubstitutionMode TypedFormalSubstitution(
    bool actual_is_variable_lvalue) {
  // §16.8.1: an actual that is a variable_lvalue keeps its mutation
  // semantics — the formal acts as the lvalue and writes back to the
  // actual. Otherwise the actual is cast to the formal's type before being
  // spliced into the body during rewriting (§F.4.1).
  return actual_is_variable_lvalue
             ? TypedFormalSubstitutionMode::kAssignBackAfterUpdate
             : TypedFormalSubstitutionMode::kCastBeforeSubstitution;
}

bool IsUntypedKeywordRequired(bool prev_formal_in_list_was_typed,
                              bool this_formal_intended_untyped) {
  // §16.8.1: the keyword is mandatory exactly when an intended-untyped
  // formal would otherwise inherit the data type of a preceding typed
  // formal in the list.
  return prev_formal_in_list_was_typed && this_formal_intended_untyped;
}

bool IsEventTypedFormalCompatibleWithEdgeIdentifierUse(
    bool formal_typed_event, bool actual_combined_with_edge_identifier) {
  // §16.8.1: an event-typed formal is incompatible with an actual that will
  // be combined with an edge_identifier; every other combination is fine.
  return !(formal_typed_event && actual_combined_with_edge_identifier);
}

}  // namespace delta
