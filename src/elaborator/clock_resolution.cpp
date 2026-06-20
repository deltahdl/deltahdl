#include "elaborator/clock_resolution.h"

namespace delta {

AssertionLeadingClock ResolveConcurrentAssertionClock(
    std::string_view explicit_clock, std::string_view inferred_clock,
    std::string_view default_clock) {
  // Rule (d): an explicit leading clocking event overrides everything else.
  if (!explicit_clock.empty()) {
    return {LeadingClockOrigin::kExplicit, std::string(explicit_clock)};
  }
  // Rule (c): a clock inferred from the enclosing procedural block supersedes
  // the default clocking event.
  if (!inferred_clock.empty()) {
    return {LeadingClockOrigin::kInferred, std::string(inferred_clock)};
  }
  // Rule (a): the default clocking event applies only when nothing else does.
  if (!default_clock.empty()) {
    return {LeadingClockOrigin::kDefault, std::string(default_clock)};
  }
  // None of the three sources supplies a clock; legality then falls to the
  // maximal-property check of rule (f).
  return {LeadingClockOrigin::kNone, std::string()};
}

bool DefaultClockAppliesToDeclaration(bool declared_in_default_clocking_block) {
  // A declaration is reached by the default clock only from inside a clocking
  // block whose own clocking event is the default.
  return declared_in_default_clocking_block;
}

bool ClockingBlockDeclarationIsLegal(bool has_explicit_clock) {
  // An explicit clocking event on a declaration inside a clocking block is
  // disallowed; only declarations without one are legal there.
  return !has_explicit_clock;
}

std::string ClockingBlockDeclarationLeadingClock(std::string_view block_clock) {
  // The block's clocking event becomes the declaration's leading clock.
  return std::string(block_clock);
}

bool ClockingBlockMulticlockedDeclarationIsLegal(bool is_multiclocked) {
  // Multiclocked sequences and properties cannot be declared in a clocking
  // block.
  return !is_multiclocked;
}

bool ClockingBlockExternalInstanceIsLegal(bool instance_is_multiclocked,
                                          std::string_view instance_clock,
                                          std::string_view block_clock) {
  // The instance must be singly clocked and share the block's clocking event.
  if (instance_is_multiclocked) {
    return false;
  }
  return instance_clock == block_clock;
}

bool MulticlockedMaximalPropertyIsLegal(const LeadingClockSet& clock_set) {
  // Per §16.16.1 a unique semantic leading clock is a singleton set whose sole
  // element is a real clocking event (not the inherited sentinel).
  return HasUniqueSemanticLeadingClock(clock_set);
}

bool UnclockedAssertionIsLegal(bool maximal_property_is_instance,
                               bool instance_has_unique_leading_clock) {
  // With no clock from rules (a), (c), or (d), the maximal property has to be a
  // sequence/property instance that itself determines a unique leading clock.
  return maximal_property_is_instance && instance_has_unique_leading_clock;
}

}  // namespace delta
