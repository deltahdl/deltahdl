#pragma once

#include <cstdint>
#include <string_view>

#include "elaborator/sampled_value.h"

namespace delta {

// §16.12.14: a property is an abort property when it has one of the forms
// accept_on, reject_on, sync_accept_on, or sync_reject_on, each applied to an
// abort condition (an expression_or_dist) and an underlying property_expr.
enum class AbortOperator : uint8_t {
  kAcceptOn,
  kRejectOn,
  kSyncAcceptOn,
  kSyncRejectOn,
};

// §16.12.14: recognize an abort operator keyword (the leading keyword of an
// abort property form). On a match, sets `out` and returns true.
bool ClassifyAbortOperator(std::string_view keyword, AbortOperator& out);

// §16.12.14: convenience predicate for the keyword classifier above.
bool IsAbortOperator(std::string_view keyword);

// §16.12.14: accept_on and reject_on are the asynchronous abort properties;
// sync_accept_on and sync_reject_on are the synchronous abort properties.
bool IsSynchronousAbort(AbortOperator op);

// §16.12.14: the accept forms (accept_on, sync_accept_on) force the overall
// property evaluation to true when the abort condition becomes true; the reject
// forms (reject_on, sync_reject_on) force it to false. This reports which
// polarity an operator carries.
bool AbortConditionForcesTrue(AbortOperator op);

// §16.12.14: any nesting of the abort operators accept_on, reject_on,
// sync_accept_on, and sync_reject_on is allowed.
bool AbortOperatorsMayNest();

// §16.12.14: abort conditions shall not contain any reference to local
// variables nor to the sequence methods triggered and matched. These report the
// per-entity permission (all forbidden).
bool AbortConditionAllowsLocalVariableReference();
bool AbortConditionAllowsTriggeredMethod();
bool AbortConditionAllowsMatchedMethod();

// §16.12.14: combined legality of an abort condition's contents per the rule
// above. The condition is legal only when it references none of the forbidden
// entities.
bool AbortConditionContentIsLegal(bool references_local_variable,
                                  bool references_triggered_method,
                                  bool references_matched_method);

// §16.12.14: an abort condition may contain sampled value functions (see
// §16.9.3). When a sampled value function other than $sampled is used in the
// abort condition, its clock argument shall be explicitly specified. This
// reports when the explicit clock argument is required.
bool AbortConditionSampledValueRequiresExplicitClock(SampledValueFunction fn);

// §16.12.14: legality of a sampled value function used inside an abort
// condition given whether its clock argument was explicitly specified. Only
// $sampled may omit the explicit clock argument.
bool AbortConditionSampledValueClockIsWellFormed(
    SampledValueFunction fn, bool clock_explicitly_specified);

}  // namespace delta
