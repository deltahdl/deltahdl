#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

// §16.9.4: the global clocking past and future sampled value functions access
// the nearest past or future value of an expression as sampled by the global
// clock. The past functions are $past_gclk, $rose_gclk, $fell_gclk,
// $stable_gclk, and $changed_gclk; the future functions are $future_gclk,
// $rising_gclk, $falling_gclk, $steady_gclk, and $changing_gclk.
enum class GlobalClockingSampledFunction : uint8_t {
  kPastGclk,
  kRoseGclk,
  kFellGclk,
  kStableGclk,
  kChangedGclk,
  kFutureGclk,
  kRisingGclk,
  kFallingGclk,
  kSteadyGclk,
  kChangingGclk,
};

// §16.9.4: recognize a global clocking sampled value function name (including
// the leading '$'). On a match, sets `out` and returns true.
bool ClassifyGlobalClockingSampledFunction(std::string_view name,
                                           GlobalClockingSampledFunction& out);

// §16.9.4: convenience predicate for the name classifier above.
bool IsGlobalClockingSampledFunction(std::string_view name);

// §16.9.4: the past functions read a value sampled at or before the current
// tick; the future functions read a value sampled at the next global tick.
bool IsGlobalClockingPastFunction(GlobalClockingSampledFunction fn);
bool IsGlobalClockingFutureFunction(GlobalClockingSampledFunction fn);

// §16.9.4: a context in which a global clocking sampled value function might
// appear. The future functions are restricted to property and sequence
// expressions; the past functions are additionally usable in general procedural
// code and in action blocks.
enum class GlobalClockingFunctionPlace : uint8_t {
  kPropertyExpr,
  kSequenceExpr,
  kActionBlock,
  kProceduralCode,
};

// §16.9.4: the requirement that these functions be used only if global clocking
// is defined is enforced during elaboration by
// Elaborator::ValidateGclkRequiresGlobalClocking, which drives the classifier
// above over real source rather than a standalone predicate.

// §16.9.4: the global clocking future sampled value functions may be invoked
// only in a property_expr or a sequence_expr; in particular they shall not be
// used in assertion action blocks.
bool GlobalClockingFutureFunctionAllowedIn(GlobalClockingFunctionPlace place);

// §16.9.4: the global clocking past sampled value functions are a special case
// of the ordinary sampled value functions and are usable everywhere those are,
// including general procedural code and action blocks.
bool GlobalClockingPastFunctionAllowedIn(GlobalClockingFunctionPlace place);

// §16.9.4: the global clocking future sampled value functions shall not be
// nested. Returns whether a use is permitted given whether it is nested inside
// another such function.
bool GlobalClockingFutureFunctionNestingAllowed(bool nested_in_future_function);

// §16.9.4: the global clocking future sampled value functions shall not be used
// in assertions containing sequence match items. Returns whether a use is
// permitted given whether the enclosing assertion contains a sequence match
// item.
bool GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(
    bool assertion_has_sequence_match_items);

}  // namespace delta
