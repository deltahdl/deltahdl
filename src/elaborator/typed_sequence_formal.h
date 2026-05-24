#pragma once

#include <cstdint>

namespace delta {

// §16.8.1: a formal argument's data type may be `untyped` (a keyword), or it
// may be one of the types allowed in §16.6, or `sequence`, or `event`. This
// enum captures the type categories that affect the §16.8.1 rules.
enum class SequenceFormalTypeKind : uint8_t {
  kUntyped,
  kSequence,
  kEvent,
  kIntegralOrUserType,
  kForbidden,
};

// §16.8.1: a formal argument shall be untyped if its data type is `untyped`.
// Conversely, a typed formal must use one of the categories listed above.
bool IsSequenceFormalTypeAllowed(SequenceFormalTypeKind kind);

// §16.8.1: a typed formal of type `sequence` may be referenced only in a
// place where a sequence_expr is legal, or as the operand of the sequence
// methods `triggered` and `matched`.
enum class SequenceTypedFormalRefPlace : uint8_t {
  kSequenceExprPosition,
  kTriggeredMethodOperand,
  kMatchedMethodOperand,
  kOtherPosition,
};

bool IsSequenceTypedFormalRefLegal(SequenceTypedFormalRefPlace where);

// §16.8.1: a typed formal of type `event` may be referenced only in places
// where an event_expression may be written.
bool IsEventTypedFormalRefLegal(bool in_event_expression_position);

// §16.8.1 (cross-link to §16.9.2): a formal of type `sequence` may not be
// the expression_or_dist operand of a goto_repetition. The §16.9.2 rules say
// goto_repetition is allowed only on Boolean expressions; sequence-typed
// formals therefore fail at the same rule from a different angle.
bool IsSequenceTypedFormalAllowedAsGotoOperand();

// §16.8.1 (cross-link to §16.11): a reference to a typed formal inside a
// sequence_match_item shall not stand as the variable_lvalue in either an
// operator_assignment or an inc_or_dec_expression — unless the formal is a
// local variable formal (defined in §16.8.2, §16.12.19).
bool IsTypedFormalAllowedAsMatchItemLvalue(bool is_local_var_formal);

// §16.8.1: if a typed formal is referenced inside a cycle_delay_range, a
// boolean_abbrev, or a sequence_abbrev (all from §16.9.2), then the type of
// the formal shall be shortint, int, or longint.
enum class SequenceFormalIntegralType : uint8_t {
  kShortint,
  kInt,
  kLongint,
  kOtherIntegral,
};

bool IsDelayOrRepetitionIndexTypeAllowed(SequenceFormalIntegralType t);

// §16.8.1: a typed formal whose actual argument is a variable_lvalue is
// treated as having the formal's type, with any assignment to the formal
// modeled as a subsequent assignment from the formal back to the actual.
// Otherwise (the actual is not a variable_lvalue), the actual is cast to the
// formal's type before being substituted in the rewriting algorithm
// (§F.4.1).
enum class TypedFormalSubstitutionMode : uint8_t {
  kAssignBackAfterUpdate,
  kCastBeforeSubstitution,
};

TypedFormalSubstitutionMode TypedFormalSubstitution(
    bool actual_is_variable_lvalue);

// §16.8.1: the keyword `untyped` shall be used when an untyped formal
// follows a data type in the formal argument list. A formal that supplies
// only a name otherwise inherits the preceding formal's data type, so an
// intended-untyped formal that trails a typed one must spell `untyped`
// explicitly. Returns true when the explicit keyword is mandatory.
bool IsUntypedKeywordRequired(bool prev_formal_in_list_was_typed,
                              bool this_formal_intended_untyped);

// §16.8.1: if an actual argument expression is meant to be combined with an
// edge_identifier to form an event_expression, the corresponding formal
// shall not be typed `event`. Returns true when the declaration is legal.
bool IsEventTypedFormalCompatibleWithEdgeIdentifierUse(
    bool formal_typed_event, bool actual_combined_with_edge_identifier);

}  // namespace delta
