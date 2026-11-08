#include "elaborator/let_construct.h"

#include <vector>

#include "parser/ast_type.h"

namespace delta {

bool WritesLetFormalType(const DataType& type) {
  return type.kind != DataTypeKind::kImplicit ||
         type.packed_dim_left != nullptr || type.signing_written;
}

std::vector<const DataType*> LetFormalTypes(
    const std::vector<FunctionArg>& formals) {
  std::vector<const DataType*> types;
  types.reserve(formals.size());
  const DataType* written = nullptr;
  for (const FunctionArg& formal : formals) {
    if (formal.is_untyped || formal.data_type.type_ref_expr != nullptr) {
      written = nullptr;
    } else if (WritesLetFormalType(formal.data_type)) {
      written = &formal.data_type;
    }
    types.push_back(written);
  }
  return types;
}

bool IsLetFormalTypeAllowed(LetFormalTypeKind kind) {
  switch (kind) {
    case LetFormalTypeKind::kUntyped:
    case LetFormalTypeKind::kEvent:
    case LetFormalTypeKind::kAssertionExpressionType:
      return true;
    case LetFormalTypeKind::kForbidden:
      return false;
  }
  return false;
}

bool IsLetEventFormalActualLegal(bool actual_is_event_expression) {
  return actual_is_event_expression;
}

bool IsLetEventTypedFormalRefLegal(bool in_event_expression_position) {
  return in_event_expression_position;
}

bool IsLetNonEventFormalActualLegal(bool self_determined_type_cast_compatible) {
  return self_determined_type_cast_compatible;
}

LetTypedFormalSubstitutionMode LetTypedFormalSubstitution(
    bool formal_is_event) {
  return formal_is_event
             ? LetTypedFormalSubstitutionMode::kEventExpressionSubstitution
             : LetTypedFormalSubstitutionMode::kCastBeforeSubstitution;
}

bool IsLetUseAfterDeclarationLegal(bool declared_before_use) {
  return declared_before_use;
}

bool IsLetReferenceLegal(bool is_hierarchical_reference) {
  return !is_hierarchical_reference;
}

bool IsLetSampledValueClockResolved(LetSampledValueClockStatus status) {
  switch (status) {
    case LetSampledValueClockStatus::kExplicit:
    case LetSampledValueClockStatus::kInferredFromContext:
      return true;
    case LetSampledValueClockStatus::kRequiredButNotInferable:
      return false;
  }
  return false;
}

}  // namespace delta
