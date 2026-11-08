#pragma once

#include <cstdint>

namespace delta {

class DiagEngine;
struct ModuleItem;

enum class SequenceFormalTypeKind : uint8_t {
  kUntyped,
  kSequence,
  kEvent,
  kIntegralOrUserType,
  kForbidden,
};

bool IsSequenceFormalTypeAllowed(SequenceFormalTypeKind kind);

enum class SequenceTypedFormalRefPlace : uint8_t {
  kSequenceExprPosition,
  kTriggeredMethodOperand,
  kMatchedMethodOperand,
  kOtherPosition,
};

bool IsSequenceTypedFormalRefLegal(SequenceTypedFormalRefPlace where);

bool IsEventTypedFormalRefLegal(bool in_event_expression_position);

bool IsSequenceTypedFormalAllowedAsGotoOperand();

bool IsTypedFormalAllowedAsMatchItemLvalue(bool is_local_var_formal);

enum class SequenceFormalIntegralType : uint8_t {
  kShortint,
  kInt,
  kLongint,
  kOtherIntegral,
};

bool IsDelayOrRepetitionIndexTypeAllowed(SequenceFormalIntegralType t);

enum class TypedFormalSubstitutionMode : uint8_t {
  kAssignBackAfterUpdate,
  kCastBeforeSubstitution,
};

TypedFormalSubstitutionMode TypedFormalSubstitution(
    bool actual_is_variable_lvalue);

bool IsUntypedKeywordRequired(bool prev_formal_in_list_was_typed,
                              bool this_formal_intended_untyped);

bool IsEventTypedFormalCompatibleWithEdgeIdentifierUse(
    bool formal_typed_event, bool actual_combined_with_edge_identifier);

void CheckTypedFormalReferences(const ModuleItem* decl, DiagEngine& diag);

}  // namespace delta
