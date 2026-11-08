#ifndef DELTA_ELABORATOR_INFERRED_CLOCK_DISABLE_H
#define DELTA_ELABORATOR_INFERRED_CLOCK_DISABLE_H

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

enum class InferredFunction : uint8_t {
  kNone,
  kClock,
  kDisable,
};

InferredFunction ClassifyInferredFunction(
    std::string_view system_function_name);

bool IsElaborationTimeInferredFunction(InferredFunction function);

struct InferredClockResolution {
  bool is_error;
  std::string event;
};

InferredClockResolution ResolveInferredClock(
    std::string_view resolved_event_expression);

std::string ResolveInferredDisable(bool within_default_disable_scope,
                                   std::string_view default_disable_condition);

enum class DefaultValuePosition : uint8_t {
  kEntireDefaultValue,
  kPartOfDefaultValue,
  kNotADefaultValue,
};

enum class FormalArgumentOwner : uint8_t {
  kProperty,
  kSequence,
  kChecker,
  kOther,
};

bool InferredFunctionPlacementIsLegal(FormalArgumentOwner owner,
                                      DefaultValuePosition position);

enum class FormalArgumentType : uint8_t {
  kUntyped,
  kEvent,
  kOther,
};

bool InferredClockFormalArgumentTypeIsLegal(FormalArgumentType type);

enum class InstantiationContext : uint8_t {
  kTopLevelAssertionInstance,
  kNestedPropertyInstance,
  kCheckerInstance,
};

enum class InferredClockReplacement : uint8_t {
  kAssertionStatementLocation,
  kClockFlowUpToInstance,
  kCheckerInstanceLocation,
};

InferredClockReplacement InferredClockReplacementSource(
    InstantiationContext context);

}  // namespace delta

#endif
