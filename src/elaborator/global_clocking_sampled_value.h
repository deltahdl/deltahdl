#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

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

bool ClassifyGlobalClockingSampledFunction(std::string_view name,
                                           GlobalClockingSampledFunction& out);

bool IsGlobalClockingSampledFunction(std::string_view name);

bool IsGlobalClockingPastFunction(GlobalClockingSampledFunction fn);
bool IsGlobalClockingFutureFunction(GlobalClockingSampledFunction fn);

enum class GlobalClockingFunctionPlace : uint8_t {
  kPropertyExpr,
  kSequenceExpr,
  kActionBlock,
  kProceduralCode,
};

bool GlobalClockingFutureFunctionAllowedIn(GlobalClockingFunctionPlace place);

bool GlobalClockingPastFunctionAllowedIn(GlobalClockingFunctionPlace place);

bool GlobalClockingFutureFunctionNestingAllowed(bool nested_in_future_function);

bool GlobalClockingFutureFunctionAllowedWithSequenceMatchItems(
    bool assertion_has_sequence_match_items);

}  // namespace delta
