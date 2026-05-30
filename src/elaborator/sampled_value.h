#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

// §16.9.3: the sampled value functions provide access to sampled values of an
// expression. $sampled reads the current sampled value; the value change
// functions ($rose, $fell, $stable, $changed) detect a change (or its absence)
// in the sampled value; $past reads a sampled value from the past.
enum class SampledValueFunction : uint8_t {
  kSampled,
  kRose,
  kFell,
  kStable,
  kChanged,
  kPast,
};

// §16.9.3: recognize a system function name (including the leading '$'). On a
// match, sets `out` to the corresponding function and returns true.
bool ClassifySampledValueFunction(std::string_view name,
                                  SampledValueFunction& out);

// §16.9.3: convenience predicate for the name classifier above.
bool IsSampledValueFunction(std::string_view name);

// §16.9.3: $rose, $fell, $stable, and $changed are the value change functions;
// they detect a change, or for $stable a lack of change, in the sampled value.
bool IsValueChangeFunction(SampledValueFunction fn);

// §16.9.3: the clocking event is required for the semantics of $past, $rose,
// $stable, $changed, and $fell. The function $sampled does not use a clocking
// event.
bool SampledValueFunctionUsesClockingEvent(SampledValueFunction fn);

// §16.9.3: the result of a value change function is true or false and may be
// used as a Boolean expression. $sampled and $past instead return the value of
// their (sampled) argument.
bool SampledValueFunctionResultIsBoolean(SampledValueFunction fn);

// §16.9.3: local variables (see §16.10) and the sequence method `matched` are
// not allowed in the argument expressions passed to the sampled value
// functions.
bool SampledValueArgumentIsLegal(bool argument_uses_local_variable,
                                 bool argument_uses_matched_method);

// §16.9.3: number_of_ticks for $past shall be 1 or greater (and shall be an
// elaboration-time constant expression). This predicate covers the 1-or-greater
// requirement on the resolved value.
bool IsPastNumberOfTicksWellFormed(long long number_of_ticks);

// §16.9.3: if number_of_ticks is not specified, it defaults to 1.
inline constexpr long long kDefaultPastNumberOfTicks = 1;

// §16.9.3: $past returns the sampled value of expression1 from the
// number_of_ticks-th strictly prior time step in which the (gated) clocking
// event occurred. If fewer than number_of_ticks such prior time steps exist,
// $past instead returns the default sampled value of expression1. This
// predicate reports when that fallback applies.
bool PastUsesDefaultSampledValue(long long number_of_ticks,
                                 long long available_prior_ticks);

// §16.9.3: if expression2 (the gating expression for the clocking event) is not
// specified, it defaults to 1'b1.
inline constexpr unsigned kDefaultPastGatingExpression = 1;

// §16.9.3: the operand roles of a $past call. expression1 is the sampled
// expression; expression2 is the gating expression for the clocking event.
enum class PastArgumentRole : uint8_t {
  kExpression1,
  kNumberOfTicks,
  kGatingExpression,
  kClockingEvent,
};

// §16.9.3: $past may refer to automatic variables (e.g., procedural loop
// variables) in its sampled expression, but it is illegal to use automatic
// variables in clocking events and in expression2 of $past.
bool PastArgumentMayReferenceAutomaticVariable(PastArgumentRole role);

}  // namespace delta
