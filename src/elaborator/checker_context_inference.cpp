#include "elaborator/checker_context_inference.h"

namespace delta {

CheckerArgumentValueSource ResolveCheckerArgumentValueSource(
    bool connected_explicitly, bool default_is_context_value_function) {
  // §17.4: an explicitly connected formal keeps its supplied actual and is not
  // subject to inference, even if it also declares a context value function
  // default. Only an omitted optional formal falls back to its default, which
  // is taken from the instantiation context when it is a context value
  // function.
  if (connected_explicitly) {
    return CheckerArgumentValueSource::kExplicitActual;
  }
  if (default_is_context_value_function) {
    return CheckerArgumentValueSource::kContextInferredDefault;
  }
  return CheckerArgumentValueSource::kOrdinaryDefault;
}

ContextValueDefaultEvaluationSite CheckerContextValueDefaultEvaluationSite() {
  // §17.4: the default values of a checker's formals are taken from the
  // instantiation context, letting one declaration adapt to each instance.
  return ContextValueDefaultEvaluationSite::kInstantiationContext;
}

}  // namespace delta
