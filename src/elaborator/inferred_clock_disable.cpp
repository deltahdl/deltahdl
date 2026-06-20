#include "elaborator/inferred_clock_disable.h"

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
  // §16.14.7: with no current resolved event expression in scope, an error
  // shall be issued; otherwise that expression is the inferred clocking event.
  if (resolved_event_expression.empty()) {
    return {/*is_error=*/true, /*event=*/std::string()};
  }
  return {/*is_error=*/false, std::string(resolved_event_expression)};
}

std::string ResolveInferredDisable(bool within_default_disable_scope,
                                   std::string_view default_disable_condition) {
  // §16.14.7: within a default disable iff scope the inferred condition is that
  // declaration's condition; outside any such scope the call returns 1'b0.
  if (within_default_disable_scope) {
    return std::string(default_disable_condition);
  }
  return "1'b0";
}

bool InferredFunctionPlacementIsLegal(FormalArgumentOwner owner,
                                      DefaultValuePosition position) {
  // §16.14.7: legal only as the entire default value of a formal argument that
  // belongs to a property, sequence, or checker declaration.
  const bool kOwnerAllows = owner == FormalArgumentOwner::kProperty ||
                            owner == FormalArgumentOwner::kSequence ||
                            owner == FormalArgumentOwner::kChecker;
  return kOwnerAllows && position == DefaultValuePosition::kEntireDefaultValue;
}

bool InferredClockFormalArgumentTypeIsLegal(FormalArgumentType type) {
  // §16.14.7: $inferred_clock may default only an untyped or event formal.
  return type == FormalArgumentType::kUntyped ||
         type == FormalArgumentType::kEvent;
}

InferredClockReplacement InferredClockReplacementSource(
    InstantiationContext context) {
  // §16.14.7: the replacement event expression is the one determined at the
  // point of instantiation, which differs by context.
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
