#ifndef DELTA_ELABORATOR_INFERRED_CLOCK_DISABLE_H
#define DELTA_ELABORATOR_INFERRED_CLOCK_DISABLE_H

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

// §16.14.7 defines two elaboration-time system functions, $inferred_clock and
// $inferred_disable, that query the clocking event and disable condition
// inferred at the point where a property, sequence, or checker is instantiated.
// The rules modeled here are the elaboration-time semantics defined by the text
// of §16.14.7; the disable-condition scoping they build on belongs to §16.15.

// §16.14.7: the two elaboration-time system functions, plus a "none" tag for a
// system-function name that is neither.
enum class InferredFunction : uint8_t {
  kNone,
  // $inferred_clock returns the inferred clocking event.
  kClock,
  // $inferred_disable returns the inferred disable condition.
  kDisable,
};

// §16.14.7: classify a system-function name as $inferred_clock,
// $inferred_disable, or neither. The names are matched including their leading
// '$'.
InferredFunction ClassifyInferredFunction(
    std::string_view system_function_name);

// §16.14.7: both inferred functions are resolved during elaboration ("the
// following elaboration-time system functions"), not at run time. Returns true
// for either inferred function and false for an unrelated system function.
bool IsElaborationTimeInferredFunction(InferredFunction function);

// §16.14.7: the outcome of resolving $inferred_clock at its call site. The
// inferred clocking event is the current resolved event expression obtained by
// applying clock flow rules up to the call. When no such event expression is in
// scope, an error shall be issued instead of producing an event.
struct InferredClockResolution {
  bool is_error;
  std::string event;
};

// §16.14.7: resolve $inferred_clock given the event expression that clock flow
// rules make current at the call site. An empty `resolved_event_expression`
// denotes that no current resolved event expression exists, which shall be
// reported as an error; otherwise that event expression is the inferred clock.
InferredClockResolution ResolveInferredClock(
    std::string_view resolved_event_expression);

// §16.14.7: resolve $inferred_disable. When the call lies within the scope of a
// default disable iff declaration (scoping per §16.15), the result is that
// declaration's disable condition. Otherwise the call returns the constant
// 1'b0 (false). An empty `default_disable_condition` together with
// `within_default_disable_scope` set is not expected; the scope flag alone
// selects between the two cases.
std::string ResolveInferredDisable(bool within_default_disable_scope,
                                   std::string_view default_disable_condition);

// §16.14.7: where in the source an inferred function call may legally appear.
// It may only be the entire default value expression of a formal argument, so a
// call that forms only part of a default value, or that appears outside any
// formal-argument default, is illegal.
enum class DefaultValuePosition : uint8_t {
  // The inferred call is the whole default value expression of a formal arg.
  kEntireDefaultValue,
  // The inferred call is a subexpression of a formal arg's default value.
  kPartOfDefaultValue,
  // The inferred call appears somewhere other than a formal-argument default.
  kNotADefaultValue,
};

// §16.14.7: the kind of declaration that owns the formal argument whose default
// value is the inferred call. Only property, sequence, and checker declarations
// may take such a default.
enum class FormalArgumentOwner : uint8_t {
  kProperty,
  kSequence,
  kChecker,
  // Any other declaration that can take a formal argument (e.g. a function,
  // task, or module), none of which may default a formal to an inferred call.
  kOther,
};

// §16.14.7: an inferred clocking or disable function shall only be used as the
// entire default value expression for a formal argument to a property,
// sequence, or checker declaration. Returns true exactly when both conditions
// hold.
bool InferredFunctionPlacementIsLegal(FormalArgumentOwner owner,
                                      DefaultValuePosition position);

// §16.14.7: the declared type of the formal argument that defaults to a
// $inferred_clock call. $inferred_clock may only default a formal that is
// untyped or of type event.
enum class FormalArgumentType : uint8_t {
  kUntyped,
  kEvent,
  // Any other explicit type (e.g. logic, bit, an integral type), which may not
  // be defaulted to $inferred_clock.
  kOther,
};

// §16.14.7: $inferred_clock shall only be used as the default value for a
// formal argument that is untyped or of type event. Returns true exactly for
// those two cases.
bool InferredClockFormalArgumentTypeIsLegal(FormalArgumentType type);

// §16.14.7: the instantiation context that determines which event expression
// replaces a $inferred_clock call when the enclosing property, sequence, or
// checker is instantiated.
enum class InstantiationContext : uint8_t {
  // The property or sequence instance is the top-level property expression of
  // an assertion statement.
  kTopLevelAssertionInstance,
  // The property or sequence instance is nested within a larger property
  // expression rather than being its top level.
  kNestedPropertyInstance,
  // The instance is a checker instance.
  kCheckerInstance,
};

// §16.14.7: where the replacement event expression for a $inferred_clock call
// is taken from, selected by the instantiation context.
enum class InferredClockReplacement : uint8_t {
  // Determined at the location of the assertion statement.
  kAssertionStatementLocation,
  // Determined by clock flow rules up to the instance location in the property
  // expression.
  kClockFlowUpToInstance,
  // Determined at the location of the checker instance.
  kCheckerInstanceLocation,
};

// §16.14.7: an inferred function call is replaced by the inferred expression as
// determined at the point where the property, sequence, or checker is
// instantiated. For $inferred_clock this source depends on the instantiation
// context: a top-level assertion instance uses the assertion statement's
// location, a nested instance uses clock flow up to the instance location, and
// a checker instance uses the checker instance's location.
InferredClockReplacement InferredClockReplacementSource(
    InstantiationContext context);

}  // namespace delta

#endif  // DELTA_ELABORATOR_INFERRED_CLOCK_DISABLE_H
