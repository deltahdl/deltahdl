#include "elaborator/global_clocking_sampled_value.h"

namespace delta {

bool ClassifyGlobalClockingSampledFunction(std::string_view name,
                                           GlobalClockingSampledFunction& out) {
  if (name == "$past_gclk") {
    out = GlobalClockingSampledFunction::kPastGclk;
    return true;
  }
  if (name == "$rose_gclk") {
    out = GlobalClockingSampledFunction::kRoseGclk;
    return true;
  }
  if (name == "$fell_gclk") {
    out = GlobalClockingSampledFunction::kFellGclk;
    return true;
  }
  if (name == "$stable_gclk") {
    out = GlobalClockingSampledFunction::kStableGclk;
    return true;
  }
  if (name == "$changed_gclk") {
    out = GlobalClockingSampledFunction::kChangedGclk;
    return true;
  }
  if (name == "$future_gclk") {
    out = GlobalClockingSampledFunction::kFutureGclk;
    return true;
  }
  if (name == "$rising_gclk") {
    out = GlobalClockingSampledFunction::kRisingGclk;
    return true;
  }
  if (name == "$falling_gclk") {
    out = GlobalClockingSampledFunction::kFallingGclk;
    return true;
  }
  if (name == "$steady_gclk") {
    out = GlobalClockingSampledFunction::kSteadyGclk;
    return true;
  }
  if (name == "$changing_gclk") {
    out = GlobalClockingSampledFunction::kChangingGclk;
    return true;
  }
  return false;
}

bool IsGlobalClockingSampledFunction(std::string_view name) {
  GlobalClockingSampledFunction fn{};
  return ClassifyGlobalClockingSampledFunction(name, fn);
}

bool IsGlobalClockingPastFunction(GlobalClockingSampledFunction fn) {
  switch (fn) {
    case GlobalClockingSampledFunction::kPastGclk:
    case GlobalClockingSampledFunction::kRoseGclk:
    case GlobalClockingSampledFunction::kFellGclk:
    case GlobalClockingSampledFunction::kStableGclk:
    case GlobalClockingSampledFunction::kChangedGclk:
      return true;
    case GlobalClockingSampledFunction::kFutureGclk:
    case GlobalClockingSampledFunction::kRisingGclk:
    case GlobalClockingSampledFunction::kFallingGclk:
    case GlobalClockingSampledFunction::kSteadyGclk:
    case GlobalClockingSampledFunction::kChangingGclk:
      return false;
  }
  return false;
}

bool IsGlobalClockingFutureFunction(GlobalClockingSampledFunction fn) {
  return !IsGlobalClockingPastFunction(fn);
}

bool GlobalClockingSampledFunctionUsable(bool global_clocking_defined) {
  return global_clocking_defined;
}

bool GlobalClockingFutureFunctionAllowedIn(GlobalClockingFunctionPlace place) {
  return place == GlobalClockingFunctionPlace::kPropertyExpr ||
         place == GlobalClockingFunctionPlace::kSequenceExpr;
}

bool GlobalClockingPastFunctionAllowedIn(GlobalClockingFunctionPlace place) {
  // §16.9.4: past functions carry the ordinary sampled-value usability, which
  // includes property and sequence expressions as well as general procedural
  // code and action blocks.
  switch (place) {
    case GlobalClockingFunctionPlace::kPropertyExpr:
    case GlobalClockingFunctionPlace::kSequenceExpr:
    case GlobalClockingFunctionPlace::kActionBlock:
    case GlobalClockingFunctionPlace::kProceduralCode:
      return true;
  }
  return false;
}

bool GlobalClockingFutureFunctionNestingAllowed(
    bool nested_in_future_function) {
  return !nested_in_future_function;
}

bool GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(
    bool assertion_has_sequence_match_items) {
  return !assertion_has_sequence_match_items;
}

}  // namespace delta
