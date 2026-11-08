#pragma once

#include <cstdint>
#include <vector>

namespace delta {

struct DataType;
struct FunctionArg;

enum class LetFormalTypeKind : uint8_t {
  kUntyped,
  kEvent,
  kAssertionExpressionType,
  kForbidden,
};

bool IsLetFormalTypeAllowed(LetFormalTypeKind kind);

bool WritesLetFormalType(const DataType& type);

std::vector<const DataType*> LetFormalTypes(
    const std::vector<FunctionArg>& formals);

bool IsLetEventFormalActualLegal(bool actual_is_event_expression);

bool IsLetEventTypedFormalRefLegal(bool in_event_expression_position);

bool IsLetNonEventFormalActualLegal(bool self_determined_type_cast_compatible);

enum class LetTypedFormalSubstitutionMode : uint8_t {
  kEventExpressionSubstitution,
  kCastBeforeSubstitution,
};

LetTypedFormalSubstitutionMode LetTypedFormalSubstitution(bool formal_is_event);

bool IsLetUseAfterDeclarationLegal(bool declared_before_use);

bool IsLetReferenceLegal(bool is_hierarchical_reference);

enum class LetSampledValueClockStatus : uint8_t {
  kExplicit,
  kInferredFromContext,
  kRequiredButNotInferable,
};

bool IsLetSampledValueClockResolved(LetSampledValueClockStatus status);

}  // namespace delta
