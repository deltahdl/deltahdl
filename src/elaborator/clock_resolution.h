#ifndef DELTA_ELABORATOR_CLOCK_RESOLUTION_H
#define DELTA_ELABORATOR_CLOCK_RESOLUTION_H

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/semantic_leading_clock.h"

namespace delta {

enum class LeadingClockOrigin : std::uint8_t {
  kNone,
  kExplicit,
  kInferred,
  kDefault,
};

struct AssertionLeadingClock {
  LeadingClockOrigin origin;
  std::string event;
};

AssertionLeadingClock ResolveConcurrentAssertionClock(
    std::string_view explicit_clock, std::string_view inferred_clock,
    std::string_view default_clock);

bool DefaultClockAppliesToDeclaration(bool declared_in_default_clocking_block);

std::string ClockingBlockDeclarationLeadingClock(std::string_view block_clock);

bool ClockingBlockExternalInstanceIsLegal(bool instance_is_multiclocked,
                                          std::string_view instance_clock,
                                          std::string_view block_clock);

bool MulticlockedMaximalPropertyIsLegal(const LeadingClockSet& clock_set);

bool UnclockedAssertionIsLegal(bool maximal_property_is_instance,
                               bool instance_has_unique_leading_clock);

}  // namespace delta

#endif
