#include "elaborator/abort_property.h"

namespace delta {

bool ClassifyAbortOperator(std::string_view keyword, AbortOperator& out) {
  if (keyword == "accept_on") {
    out = AbortOperator::kAcceptOn;
    return true;
  }
  if (keyword == "reject_on") {
    out = AbortOperator::kRejectOn;
    return true;
  }
  if (keyword == "sync_accept_on") {
    out = AbortOperator::kSyncAcceptOn;
    return true;
  }
  if (keyword == "sync_reject_on") {
    out = AbortOperator::kSyncRejectOn;
    return true;
  }
  return false;
}

bool IsAbortOperator(std::string_view keyword) {
  AbortOperator ignored;
  return ClassifyAbortOperator(keyword, ignored);
}

bool IsSynchronousAbort(AbortOperator op) {
  // §16.12.14: the sync_ forms are evaluated only at the clocking event and are
  // the synchronous abort properties.
  return op == AbortOperator::kSyncAcceptOn ||
         op == AbortOperator::kSyncRejectOn;
}

bool AbortConditionForcesTrue(AbortOperator op) {
  // §16.12.14: the accept variants make the overall evaluation true on abort.
  return op == AbortOperator::kAcceptOn || op == AbortOperator::kSyncAcceptOn;
}

bool AbortOperatorsMayNest() { return true; }

bool AbortConditionAllowsLocalVariableReference() { return false; }

bool AbortConditionAllowsTriggeredMethod() { return false; }

bool AbortConditionAllowsMatchedMethod() { return false; }

bool AbortConditionContentIsLegal(bool references_local_variable,
                                  bool references_triggered_method,
                                  bool references_matched_method) {
  return !references_local_variable && !references_triggered_method &&
         !references_matched_method;
}

bool AbortConditionSampledValueRequiresExplicitClock(SampledValueFunction fn) {
  // §16.12.14: only $sampled may be used without an explicit clock argument.
  return fn != SampledValueFunction::kSampled;
}

bool AbortConditionSampledValueClockIsWellFormed(
    SampledValueFunction fn, bool clock_explicitly_specified) {
  if (AbortConditionSampledValueRequiresExplicitClock(fn)) {
    return clock_explicitly_specified;
  }
  return true;
}

}  // namespace delta
