#ifndef DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_
#define DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_

#include <cstdint>

#include "common/types.h"
#include "simulator/sva_engine_sequences.h"

namespace delta {

enum class AssertionKind : uint8_t {
  kAssert = 0,
  kAssume = 1,
  kCover = 2,
  kRestrict = 3,
};

// §16.12.2: a sequence property has one of three forms — a bare sequence_expr,
// weak(sequence_expr), or strong(sequence_expr). strong and weak are the
// sequence operators that fix the evaluation strength; when neither appears the
// strength is inferred from the enclosing assertion statement.
enum class SequencePropertyStrength : uint8_t {
  kWeak = 0,
  kStrong = 1,
};

// §16.12.2: when the strong/weak operator is omitted, a bare sequence_expr is
// evaluated weakly inside assert property and assume property, and strongly
// inside every other assertion statement (e.g. cover property, restrict
// property).
SequencePropertyStrength DefaultSequencePropertyStrength(AssertionKind stmt);

// §16.12.2: strong(sequence_expr) is true if, and only if, there is a nonempty
// match of the sequence_expr. One match suffices, so this also gives
// strong(first_match(sequence_expr)).
PropertyResult EvalStrongSequenceProperty(bool has_nonempty_match);

// §16.12.2: weak(sequence_expr) is true if, and only if, no finite prefix
// witnesses inability to match the sequence_expr. A prefix witnesses inability
// for sequence_expr exactly when it does for first_match(sequence_expr), so
// this also gives weak(first_match(sequence_expr)).
PropertyResult EvalWeakSequenceProperty(bool finite_prefix_witnesses_inability);

// §16.12.3: the `not` operator switches the strength of the property it
// negates. Negating a weak property yields a strong one and vice versa, so a
// caller that knows the underlying strength can derive the negation's strength.
SequencePropertyStrength NegatePropertyStrength(SequencePropertyStrength inner);

bool IsImmediateAssertionKindAllowed(AssertionKind kind);

enum class AssertionTiming : uint8_t {
  kImmediate = 0,
  kConcurrent = 1,
};

bool ConcurrentTimingUsesSampledValues(AssertionTiming timing);

enum class SampleMode : uint8_t {
  kPreponed = 0,
  kCurrent = 1,
  kDefault = 2,
  // §16.5.1: a past or future value of an active free checker variable that is
  // referenced by a sampled value function is taken from the Postponed region
  // rather than the Preponed region.
  kPostponed = 3,
};

struct SampledValue {
  uint64_t value = 0;
  SampleMode mode = SampleMode::kPreponed;
};

SampledValue SampleStaticVariable(uint64_t preponed_value, SimTime t,
                                  uint64_t type_default);

SampledValue SampleAutomaticVariable(uint64_t current_value);

// §16.5.1: local variables (see §16.10) are one of the exceptions to the
// preponed-sample rule — like automatic and active free checker variables,
// their sampled value is their current value rather than a value read from the
// Preponed region. §16.10 restates this directly ("the sampled value of a local
// variable is the current value, see 16.5.1"). Modeling local-variable sampling
// with its own entry point keeps that weave explicit at the point production
// code consults a local variable's sampled value.
SampledValue SampleLocalVariable(uint64_t current_value);

// §16.5.1: active free checker variables are the third kind (with automatic and
// local variables) whose sampled value is their current value rather than a
// Preponed value.
SampledValue SampleActiveFreeCheckerVariable(uint64_t current_value);

// §16.5.1: exception to the current-value rule above. When a past or future
// value of an active free checker variable is referenced by a sampled value
// function (e.g. $past/$future), that value is sampled in the Postponed region.
SampledValue SampleActiveFreeCheckerVarPastFuture(uint64_t postponed_value);

// §16.5.1: complementary exception for automatic variables. When a past or
// future value of an automatic variable is referenced by a sampled value
// function, the current value of the automatic variable is taken instead of a
// value from a past or future clock tick.
SampledValue SampleAutomaticVarPastFuture(uint64_t current_value);

SampledValue DefaultSampledValueOfTriggered();
SampledValue DefaultSampledValueOfMatched();

SampledValue SampleSingleVariableExpression(SampledValue var_sample);

SampledValue SampleConstCastExpression(uint64_t argument_current_value);

SampledValue SampleProceduralAssertionArgument(uint64_t current_value);

SampledValue ProceduralArgumentValueAfterMature(
    SampledValue captured, uint64_t later_underlying_value);

enum class ProceduralExecutionEffect : uint8_t {
  kActivation = 0,
  kCompletion = 1,
};

bool ProceduralExecutionAffects(ProceduralExecutionEffect effect,
                                bool already_matured);

SampledValue SampleProceduralAssertionActionBlockArgument(
    uint64_t current_value);

bool ActionBlockMayModifyArgument();

uint64_t ReadProceduralConditionalGuard(uint64_t current_value,
                                        uint64_t sampled_value);

SampledValue SampledValueOfTriggered(bool current_returned);
SampledValue SampledValueOfMatched(bool current_returned);

SampledValue SampleRecursiveExpression(SampledValue a, SampledValue b,
                                       uint64_t (*combinator)(uint64_t,
                                                              uint64_t));

SampledValue DefaultSampledValueOfVariableOrNet(uint64_t type_default);

// §16.6: a concurrent-assertion Boolean expression's result is interpreted
// the same way as the condition of a procedural `if`. With aval/bval dual
// rails, any unknown bit (bval != 0) makes the value false; otherwise the
// value is true iff aval is non-zero.
bool InterpretAssertionExprAsBoolean(uint64_t aval, uint64_t bval);

// §16.6: an element of a dynamic array, queue, or associative array that has
// been sampled for assertion expression evaluation must keep being readable
// until the evaluation completes, even if the array is later mutated. The
// `live` flag stays true across simulated mutation to model that lifetime.
struct SampledArrayElement {
  uint64_t value = 0;
  bool live = true;
};
SampledArrayElement SampleArrayElementForAssertion(uint64_t element_value);
SampledArrayElement ArrayElementAfterArrayMutation(SampledArrayElement sampled);
bool SampledArrayElementStillReadable(const SampledArrayElement& sampled);

// §16.6: where a Boolean expression can occur inside a concurrent assertion.
// The sampled-vs-current evaluation rule branches on this context: only
// sequence/property expressions use sampled values; clocking-event expressions
// are explicitly excepted (they follow §16.5), and disable-condition
// expressions are evaluated with current values.
enum class BooleanExprPlace : uint8_t {
  kSequenceOrPropertyExpr = 0,
  kClockingEvent = 1,
  kDisableCondition = 2,
};
bool BooleanExprUsesSampledValues(BooleanExprPlace place);

// §16.6: disable-condition specifics. The condition is evaluated against
// current values; `triggered` is callable from it, but `matched` and local
// variables are not.
bool DisableConditionUsesCurrentValues();
bool DisableConditionAllowsTriggeredMethod();
bool DisableConditionAllowsMatchedMethod();
bool DisableConditionAllowsLocalVariableReference();

enum class ClockingInputSkew : uint8_t {
  kStep1 = 0,
  kOther = 1,
};

bool IsClockingBlockInputSamplingValid(ClockingInputSkew skew);

// §16.18: when a variable used in a concurrent assertion is a clocking block
// variable, it is sampled only in the clocking block. The assertion observes
// the value the clocking block already captured at its own clocking event
// (with that block's clock and skew); it does not take a second, independent
// concurrent-assertion sample of the underlying signal. A reference to a plain
// variable that is not a clocking block variable instead uses the ordinary
// concurrent-assertion sample defined in §16.5. This selects, for a variable
// referenced in a concurrent assertion, the sampled value the assertion uses.
// Because the single clocking-block sample is what every such reference reads,
// distinct ways of naming the same clocking variable (directly, through the
// clocking block, or through a property declared inside it) all observe the
// same value.
SampledValue ConcurrentAssertionVariableSample(
    bool is_clocking_block_variable, uint64_t clocking_block_sampled_value,
    SampledValue ordinary_assertion_sample);

}  // namespace delta

#endif  // DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_
