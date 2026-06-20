#ifndef DELTA_ELABORATOR_CHECKER_CONTEXT_INFERENCE_H
#define DELTA_ELABORATOR_CHECKER_CONTEXT_INFERENCE_H

#include <cstdint>

namespace delta {

// §17.4 covers context inference at a checker instantiation: how each formal
// argument of an instantiated checker obtains its effective value. A checker
// may declare a formal whose default value is a context value function (see
// §16.14.7); such a default lets the checker adapt to the place where it is
// instantiated. The rules modeled here are the per-argument resolution defined
// by the text of §17.4 — deciding, for one formal at one instantiation, whether
// its value is the explicitly connected actual or a default taken from the
// instantiation context. The semantics of the context value functions
// themselves belong to §16.14.7, and the legality of an instantiation belongs
// to §17.3.

// §17.4: the source of a checker formal argument's effective value at one
// particular instantiation.
enum class CheckerArgumentValueSource : uint8_t {
  // The instantiation connected this formal explicitly; the supplied actual
  // argument is used unchanged and no context inference takes place.
  kExplicitActual,
  // The instantiation left this optional formal unconnected and its declared
  // default is a context value function; the value is inferred from the
  // instantiation context.
  kContextInferredDefault,
  // The instantiation left this optional formal unconnected and its declared
  // default is an ordinary expression; that default expression supplies the
  // value verbatim.
  kOrdinaryDefault,
};

// §17.4: resolve where a single checker formal argument's value comes from at a
// given instantiation. A formal that the instantiation connects explicitly
// always uses its actual, even when the formal also carries a context value
// function default (as in the my_check1 instantiation, where every argument is
// supplied). An omitted optional formal falls back to its declared default;
// that default is taken from the instantiation context when it is a context
// value function (as in my_check2) and used verbatim otherwise.
CheckerArgumentValueSource ResolveCheckerArgumentValueSource(
    bool connected_explicitly, bool default_is_context_value_function);

// §17.4: where a context value function serving as a checker formal default is
// evaluated.
enum class ContextValueDefaultEvaluationSite : uint8_t {
  // Evaluated where the checker is instantiated.
  kInstantiationContext,
  // Evaluated where the checker is declared.
  kDeclarationContext,
};

// §17.4: a context value function used as a checker formal default is evaluated
// at the point where the checker is instantiated, not where it is declared, so
// a single checker declaration adapts its inferred clock and disable to each
// instantiation context.
ContextValueDefaultEvaluationSite CheckerContextValueDefaultEvaluationSite();

}  // namespace delta

#endif  // DELTA_ELABORATOR_CHECKER_CONTEXT_INFERENCE_H
