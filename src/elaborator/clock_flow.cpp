#include "elaborator/clock_flow.h"

namespace delta {

std::vector<ClockScope> ResolveOperandClocks(
    ClockFlowOperator kind, const ClockScope& incoming,
    const std::vector<ClockFlowOperand>& operands) {
  std::vector<ClockScope> resolved;
  resolved.reserve(operands.size());
  // The scope currently flowing into the next operand. For a linear operator it
  // is threaded through the operands; for a branching operator it stays at
  // `incoming` so each operand is governed independently.
  ClockScope flowing = incoming;
  for (const ClockFlowOperand& operand : operands) {
    // A clocking event written at the operand replaces the flowing scope.
    const ClockScope governing =
        operand.explicit_clock.empty() ? flowing : operand.explicit_clock;
    resolved.push_back(governing);
    if (kind == ClockFlowOperator::kLinear) {
      // The replacement persists to the operands that follow.
      flowing = governing;
    }
  }
  return resolved;
}

ClockScope ClockEnteringParentheses(const ClockScope& incoming) {
  // The surrounding scope flows into the parenthesized subexpression unchanged.
  return incoming;
}

ClockScope ClockAfterParentheses(const ClockScope& incoming,
                                 const ClockScope& /*interior_terminal*/) {
  // A clocking event introduced inside the parentheses does not flow out, so
  // the surrounding scope is unaffected by whatever clock the interior ends on.
  return incoming;
}

ClockScope ClockEnteringInstance(const ClockScope& incoming,
                                 InstanceMethod /*method*/) {
  // The scope flows into the instance regardless of whether `triggered` or
  // `matched` is applied to it.
  return incoming;
}

ClockScope ClockAfterInstance(const ClockScope& incoming,
                              const ClockScope& /*declaration_clock*/) {
  // A clocking event in the declaration of the property or sequence does not
  // flow out of the instance, so the surrounding scope is unaffected.
  return incoming;
}

ClockScope ClockEnteringDisableCondition(const ClockScope& /*incoming*/) {
  // The scope does not flow into the disable condition, which therefore carries
  // no clocking event.
  return ClockScope();
}

ClockScope JuxtaposedClockingEvent(const ClockScope& /*first*/,
                                   const ClockScope& second) {
  // The second clocking event immediately overrides (nullifies) the first.
  return second;
}

}  // namespace delta
