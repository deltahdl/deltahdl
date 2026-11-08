#ifndef DELTA_ELABORATOR_CHECKER_CONTEXT_INFERENCE_H
#define DELTA_ELABORATOR_CHECKER_CONTEXT_INFERENCE_H

#include <cstdint>

namespace delta {

enum class CheckerArgumentValueSource : uint8_t {
  kExplicitActual,
  kContextInferredDefault,
  kOrdinaryDefault,
};

CheckerArgumentValueSource ResolveCheckerArgumentValueSource(
    bool connected_explicitly, bool default_is_context_value_function);

enum class ContextValueDefaultEvaluationSite : uint8_t {
  kInstantiationContext,
  kDeclarationContext,
};

ContextValueDefaultEvaluationSite CheckerContextValueDefaultEvaluationSite();

}  // namespace delta

#endif
