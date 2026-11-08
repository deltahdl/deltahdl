#include "elaborator/clock_flow.h"

#include <vector>

namespace delta {

std::vector<ClockScope> ResolveOperandClocks(
    ClockFlowOperator kind, const ClockScope& incoming,
    const std::vector<ClockFlowOperand>& operands) {
  std::vector<ClockScope> resolved;
  resolved.reserve(operands.size());
  ClockScope flowing = incoming;
  for (const ClockFlowOperand& operand : operands) {
    const ClockScope kGoverning =
        operand.explicit_clock.empty() ? flowing : operand.explicit_clock;
    resolved.push_back(kGoverning);
    if (kind == ClockFlowOperator::kLinear) {
      flowing = kGoverning;
    }
  }
  return resolved;
}

ClockScope ClockEnteringParentheses(const ClockScope& incoming) {
  return incoming;
}

ClockScope ClockAfterParentheses(const ClockScope& incoming,
                                 const ClockScope&) {
  return incoming;
}

ClockScope ClockEnteringInstance(const ClockScope& incoming, InstanceMethod) {
  return incoming;
}

ClockScope ClockAfterInstance(const ClockScope& incoming, const ClockScope&) {
  return incoming;
}

ClockScope ClockEnteringDisableCondition(const ClockScope&) {
  return ClockScope();
}

ClockScope JuxtaposedClockingEvent(const ClockScope&,
                                   const ClockScope& second) {
  return second;
}

}  // namespace delta
