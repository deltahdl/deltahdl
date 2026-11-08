#ifndef DELTA_ELABORATOR_CLOCK_FLOW_H
#define DELTA_ELABORATOR_CLOCK_FLOW_H

#include <cstdint>
#include <string>
#include <vector>

namespace delta {

using ClockScope = std::string;

enum class ClockFlowOperator : std::uint8_t {
  kLinear,
  kBranching,
};

struct ClockFlowOperand {
  ClockScope explicit_clock;
};

std::vector<ClockScope> ResolveOperandClocks(
    ClockFlowOperator kind, const ClockScope& incoming,
    const std::vector<ClockFlowOperand>& operands);

ClockScope ClockEnteringParentheses(const ClockScope& incoming);

ClockScope ClockAfterParentheses(const ClockScope& incoming,
                                 const ClockScope& interior_terminal);

enum class InstanceMethod : std::uint8_t {
  kNone,
  kTriggered,
  kMatched,
};

ClockScope ClockEnteringInstance(const ClockScope& incoming,
                                 InstanceMethod method);

ClockScope ClockAfterInstance(const ClockScope& incoming,
                              const ClockScope& declaration_clock);

ClockScope ClockEnteringDisableCondition(const ClockScope& incoming);

ClockScope JuxtaposedClockingEvent(const ClockScope& first,
                                   const ClockScope& second);

}  // namespace delta

#endif
