#include "elaborator/checker_context_inference.h"

namespace delta {

CheckerArgumentValueSource ResolveCheckerArgumentValueSource(
    bool connected_explicitly, bool default_is_context_value_function) {
  if (connected_explicitly) {
    return CheckerArgumentValueSource::kExplicitActual;
  }
  if (default_is_context_value_function) {
    return CheckerArgumentValueSource::kContextInferredDefault;
  }
  return CheckerArgumentValueSource::kOrdinaryDefault;
}

ContextValueDefaultEvaluationSite CheckerContextValueDefaultEvaluationSite() {
  return ContextValueDefaultEvaluationSite::kInstantiationContext;
}

}  // namespace delta
