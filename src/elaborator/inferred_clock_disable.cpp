#include "elaborator/inferred_clock_disable.h"

#include <string_view>

namespace delta {

InferredFunction ClassifyInferredFunction(
    std::string_view system_function_name) {
  if (system_function_name == "$inferred_clock") {
    return InferredFunction::kClock;
  }
  if (system_function_name == "$inferred_disable") {
    return InferredFunction::kDisable;
  }
  return InferredFunction::kNone;
}

bool IsElaborationTimeInferredFunction(InferredFunction function) {
  return function != InferredFunction::kNone;
}

InferredClockResolution ResolveInferredClock(
    std::string_view resolved_event_expression) {
  if (resolved_event_expression.empty()) {
    return {true, std::string()};
  }
  return {false, std::string(resolved_event_expression)};
}

std::string ResolveInferredDisable(bool within_default_disable_scope,
                                   std::string_view default_disable_condition) {
  if (within_default_disable_scope) {
    return std::string(default_disable_condition);
  }
  return "1'b0";
}

bool InferredFunctionPlacementIsLegal(FormalArgumentOwner owner,
                                      DefaultValuePosition position) {
  const bool kOwnerAllows = owner == FormalArgumentOwner::kProperty ||
                            owner == FormalArgumentOwner::kSequence ||
                            owner == FormalArgumentOwner::kChecker;
  return kOwnerAllows && position == DefaultValuePosition::kEntireDefaultValue;
}

bool InferredClockFormalArgumentTypeIsLegal(FormalArgumentType type) {
  return type == FormalArgumentType::kUntyped ||
         type == FormalArgumentType::kEvent;
}

InferredClockReplacement InferredClockReplacementSource(
    InstantiationContext context) {
  switch (context) {
    case InstantiationContext::kTopLevelAssertionInstance:
      return InferredClockReplacement::kAssertionStatementLocation;
    case InstantiationContext::kNestedPropertyInstance:
      return InferredClockReplacement::kClockFlowUpToInstance;
    case InstantiationContext::kCheckerInstance:
      return InferredClockReplacement::kCheckerInstanceLocation;
  }
  return InferredClockReplacement::kClockFlowUpToInstance;
}

}  // namespace delta
