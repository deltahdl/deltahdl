#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

enum class SampledValueFunction : uint8_t {
  kSampled,
  kRose,
  kFell,
  kStable,
  kChanged,
  kPast,
};

bool ClassifySampledValueFunction(std::string_view name,
                                  SampledValueFunction& out);

bool IsSampledValueFunction(std::string_view name);

bool IsValueChangeFunction(SampledValueFunction fn);

bool SampledValueFunctionUsesClockingEvent(SampledValueFunction fn);

bool SampledValueFunctionResultIsBoolean(SampledValueFunction fn);

bool SampledValueArgumentIsLegal(bool argument_uses_local_variable,
                                 bool argument_uses_matched_method);

bool IsPastNumberOfTicksWellFormed(long long number_of_ticks);

inline constexpr long long kDefaultPastNumberOfTicks = 1;

bool PastUsesDefaultSampledValue(long long number_of_ticks,
                                 long long available_prior_ticks);

inline constexpr unsigned kDefaultPastGatingExpression = 1;

enum class PastArgumentRole : uint8_t {
  kExpression1,
  kNumberOfTicks,
  kGatingExpression,
  kClockingEvent,
};

bool PastArgumentMayReferenceAutomaticVariable(PastArgumentRole role);

enum class SampledValueClockContext : uint8_t {
  kAssertionSequenceOrProperty,
  kDisableConditionOrClockExpression,
  kActionBlock,
  kProcedure,
  kOutsideAssertion,
};

enum class SampledValueClockInference : uint8_t {
  kFromClockFlow,
  kRequiresExplicitClock,
  kFromLeadingClock,
  kFromProceduralContext,
  kFromDefaultClocking,
};

SampledValueClockInference InferSampledValueClockingEvent(
    SampledValueClockContext context);

}  // namespace delta
