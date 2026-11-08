#pragma once

#include <cstdint>
#include <string_view>

#include "elaborator/sampled_value.h"

namespace delta {

enum class AbortOperator : uint8_t {
  kAcceptOn,
  kRejectOn,
  kSyncAcceptOn,
  kSyncRejectOn,
};

bool ClassifyAbortOperator(std::string_view keyword, AbortOperator& out);

bool IsAbortOperator(std::string_view keyword);

bool IsSynchronousAbort(AbortOperator op);

bool AbortConditionForcesTrue(AbortOperator op);

bool AbortOperatorsMayNest();

bool AbortConditionAllowsLocalVariableReference();
bool AbortConditionAllowsTriggeredMethod();
bool AbortConditionAllowsMatchedMethod();

bool AbortConditionContentIsLegal(bool references_local_variable,
                                  bool references_triggered_method,
                                  bool references_matched_method);

bool AbortConditionSampledValueRequiresExplicitClock(SampledValueFunction fn);

bool AbortConditionSampledValueClockIsWellFormed(
    SampledValueFunction fn, bool clock_explicitly_specified);

}  // namespace delta
