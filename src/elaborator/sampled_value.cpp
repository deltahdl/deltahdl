#include "elaborator/sampled_value.h"

namespace delta {

bool ClassifySampledValueFunction(std::string_view name,
                                  SampledValueFunction& out) {
  if (name == "$sampled") {
    out = SampledValueFunction::kSampled;
    return true;
  }
  if (name == "$rose") {
    out = SampledValueFunction::kRose;
    return true;
  }
  if (name == "$fell") {
    out = SampledValueFunction::kFell;
    return true;
  }
  if (name == "$stable") {
    out = SampledValueFunction::kStable;
    return true;
  }
  if (name == "$changed") {
    out = SampledValueFunction::kChanged;
    return true;
  }
  if (name == "$past") {
    out = SampledValueFunction::kPast;
    return true;
  }
  return false;
}

bool IsSampledValueFunction(std::string_view name) {
  SampledValueFunction fn{};
  return ClassifySampledValueFunction(name, fn);
}

bool IsValueChangeFunction(SampledValueFunction fn) {
  switch (fn) {
    case SampledValueFunction::kRose:
    case SampledValueFunction::kFell:
    case SampledValueFunction::kStable:
    case SampledValueFunction::kChanged:
      return true;
    case SampledValueFunction::kSampled:
    case SampledValueFunction::kPast:
      return false;
  }
  return false;
}

bool SampledValueFunctionUsesClockingEvent(SampledValueFunction fn) {
  // §16.9.3: every sampled value function other than $sampled is given meaning
  // by a clocking event; $sampled alone does not use one.
  return fn != SampledValueFunction::kSampled;
}

bool SampledValueFunctionResultIsBoolean(SampledValueFunction fn) {
  return IsValueChangeFunction(fn);
}

bool SampledValueArgumentIsLegal(bool argument_uses_local_variable,
                                 bool argument_uses_matched_method) {
  return !argument_uses_local_variable && !argument_uses_matched_method;
}

bool IsPastNumberOfTicksWellFormed(long long number_of_ticks) {
  return number_of_ticks >= 1;
}

bool PastUsesDefaultSampledValue(long long number_of_ticks,
                                 long long available_prior_ticks) {
  return available_prior_ticks < number_of_ticks;
}

bool PastArgumentMayReferenceAutomaticVariable(PastArgumentRole role) {
  switch (role) {
    case PastArgumentRole::kExpression1:
    case PastArgumentRole::kNumberOfTicks:
      return true;
    case PastArgumentRole::kGatingExpression:
    case PastArgumentRole::kClockingEvent:
      return false;
  }
  return false;
}

SampledValueClockInference InferSampledValueClockingEvent(
    SampledValueClockContext context) {
  switch (context) {
    case SampledValueClockContext::kAssertionSequenceOrProperty:
      // The clock flow rules of §16.13.3 determine the clocking event.
      return SampledValueClockInference::kFromClockFlow;
    case SampledValueClockContext::kDisableConditionOrClockExpression:
      // No inference here: the call shall be explicitly clocked.
      return SampledValueClockInference::kRequiresExplicitClock;
    case SampledValueClockContext::kActionBlock:
      return SampledValueClockInference::kFromLeadingClock;
    case SampledValueClockContext::kProcedure:
      return SampledValueClockInference::kFromProceduralContext;
    case SampledValueClockContext::kOutsideAssertion:
      return SampledValueClockInference::kFromDefaultClocking;
  }
  return SampledValueClockInference::kRequiresExplicitClock;
}

}  // namespace delta
