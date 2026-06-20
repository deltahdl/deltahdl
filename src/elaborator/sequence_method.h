#pragma once

#include <cstdint>
#include <utility>
#include <vector>

namespace delta {

// §16.13.6: the two sequence methods that identify the end point of a sequence.
// `triggered` and `matched` are the shared vocabulary used by §16.9.11 (single
// clock composition), §16.13.5 (multiclock end-point detection), and §9.4.4
// (level-sensitive wait controls). This header is their definitional home.
enum class SequenceMethod : uint8_t {
  kTriggered,
  kMatched,
};

// §16.13.6: the operand of a sequence method shall be a named sequence instance
// (with or without arguments), an untyped formal argument, or a formal argument
// of type `sequence`, in the contexts where such arguments are legal. Any other
// operand form is not permitted.
enum class SequenceMethodOperandKind : uint8_t {
  kNamedSequenceInstance,
  kUntypedFormalArgument,
  kSequenceTypedFormalArgument,
  kOther,
};
bool IsSequenceMethodOperandLegal(SequenceMethodOperandKind kind);

// §16.13.6: the result of `triggered` and `matched` is a single-bit value,
// true (1'b1) or false (1'b0).
bool SequenceMethodResultIsSingleBit();

// §16.13.6: the result of a sequence method does not depend upon the starting
// point of the match of its operand sequence; it reflects only whether the end
// point has been reached.
bool SequenceMethodResultDependsOnStartPoint();

// §16.13.6: the syntactic context in which a sequence method is invoked.
enum class SequenceMethodContext : uint8_t {
  kAssertionStatement,
  kWaitStatement,
  kBooleanExpressionOutsideSequence,
  kSequenceExpression,
};

// §16.13.6: a sequence treats its formal argument as a local variable when the
// formal is used as the variable_lvalue of an operator_assignment or an
// inc_or_dec_expression inside a sequence_match_item.
bool SequenceTreatsFormalAsLocalVar(bool formal_is_match_item_lvalue);

// §16.13.6: `triggered` may be used in assertion statements, in `wait`
// statements (see §9.4.4), or in Boolean expressions outside a sequence
// context. It is an error to invoke `triggered` outside a sequence context on a
// sequence that treats its formal arguments as local variables. `matched` can
// only be used in sequence expressions. Returns true when the invocation is
// legal.
bool IsSequenceMethodContextLegal(SequenceMethod method,
                                  SequenceMethodContext context,
                                  bool sequence_treats_formal_as_local_var);

// §16.13.6: the triggered/matched status of a sequence is established during
// the Observed region of the time step.
bool SequenceMethodStatusSetInObservedRegion();

// §16.13.6: how long the status of a sequence method persists once established.
enum class SequenceMethodPersistence : uint8_t {
  // `triggered`: the status persists through the remainder of the time step
  // (i.e., until simulation time advances).
  kThroughTimeStep,
  // `matched`: the status is stored and persists until the arrival of the first
  // clock tick of the destination sequence after the match, providing the
  // synchronization between the two clocks.
  kUntilFirstDestinationClockTick,
};
SequenceMethodPersistence SequenceMethodStatusPersistence(
    SequenceMethod method);

// §16.13.6: the sampled value of a sequence method is defined as its current
// value (see §16.5.1).
bool SequenceMethodSampledValueIsCurrentValue();

// §16.13.6 (and §16.9.11): if a sequence admits an empty match, such empty
// matches shall not activate the `triggered` or `matched` methods. The methods
// fire only on a nonempty match.
bool EmptyMatchActivatesSequenceMethod();

// §16.13.6: there shall be no circular dependencies between sequences induced
// by the use of `triggered`. A dependency edge {a, b} records that the body of
// sequence `a` applies `triggered` to sequence `b`. Returns true when the set
// of such edges over `sequence_count` sequences contains no cycle (and is thus
// legal).
bool TriggeredSequenceDependenciesAreAcyclic(
    int sequence_count,
    const std::vector<std::pair<int, int>>& triggered_edges);

// §16.13.6: a sequence on which a method is applied shall either be clocked or
// infer its clocking event from the context where it is used, following the
// same inference rules as §16.9.3 for sampled value functions. This enumerates
// the place that supplies the clocking event.
enum class SequenceMethodClockContext : uint8_t {
  // The sequence carries its own (explicit) clocking event.
  kExplicitlyClocked,
  // Substituted into a checker instantiation: clocked as if instantiated inside
  // the checker.
  kCheckerInstantiation,
  // Connected to a port of a module instantiation: clocked as if instantiated
  // at
  // the place of module instantiation.
  kModulePortConnection,
  // Connected to a port of an interface or program instantiation: same rule as
  // a
  // module port connection.
  kInterfaceOrProgramPortConnection,
  // Passed as an actual argument to a function or task call: same rule as a
  // module port connection.
  kFunctionOrTaskArgument,
  // Instantiated in an event expression: the preceding inference rules also
  // apply here.
  kEventExpressionInstance,
  // Otherwise the clock is inferred from the surrounding context per §16.9.3.
  kInferredFromSurroundingContext,
};

// §16.13.6: returns true when the sequence's clocking event is determined by
// context inference rather than being carried explicitly on the sequence.
bool SequenceMethodClockIsInferredFromContext(SequenceMethodClockContext ctx);

// §16.13.6: if `$inferred_clock` is the default value for a formal argument of
// a sequence (see §16.14.7) and an actual argument is not provided to the
// instance to which a method is applied, the §16.9.3 inference rules are used
// to determine the clocking event bound to that formal. Returns true when those
// inference rules apply (i.e., no actual argument was supplied).
bool InferredClockDefaultUsesSampledValueRules(bool actual_argument_provided);

}  // namespace delta
