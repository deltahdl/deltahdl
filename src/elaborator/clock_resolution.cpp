#include "elaborator/clock_resolution.h"

#include <string>
#include <string_view>

#include "elaborator/semantic_leading_clock.h"

namespace delta {

AssertionLeadingClock ResolveConcurrentAssertionClock(
    std::string_view explicit_clock, std::string_view inferred_clock,
    std::string_view default_clock) {
  if (!explicit_clock.empty()) {
    return {LeadingClockOrigin::kExplicit, std::string(explicit_clock)};
  }
  if (!inferred_clock.empty()) {
    return {LeadingClockOrigin::kInferred, std::string(inferred_clock)};
  }
  if (!default_clock.empty()) {
    return {LeadingClockOrigin::kDefault, std::string(default_clock)};
  }
  return {LeadingClockOrigin::kNone, std::string()};
}

bool DefaultClockAppliesToDeclaration(bool declared_in_default_clocking_block) {
  return declared_in_default_clocking_block;
}

std::string ClockingBlockDeclarationLeadingClock(std::string_view block_clock) {
  return std::string(block_clock);
}

bool ClockingBlockExternalInstanceIsLegal(bool instance_is_multiclocked,
                                          std::string_view instance_clock,
                                          std::string_view block_clock) {
  if (instance_is_multiclocked) {
    return false;
  }
  return instance_clock == block_clock;
}

bool MulticlockedMaximalPropertyIsLegal(const LeadingClockSet& clock_set) {
  return HasUniqueSemanticLeadingClock(clock_set);
}

bool UnclockedAssertionIsLegal(bool maximal_property_is_instance,
                               bool instance_has_unique_leading_clock) {
  return maximal_property_is_instance && instance_has_unique_leading_clock;
}

}  // namespace delta
