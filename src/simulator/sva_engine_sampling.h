#ifndef DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_
#define DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_

#include <cstdint>
#include <unordered_map>

#include "common/types.h"
#include "simulator/sva_engine_sequences.h"

namespace delta {

class Arena;
struct Variable;

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

// §16.5.1: the sampled values of the variables that clocked concurrent
// assertions read.
//
// §16.5.1 states the rule this holds: "The sampled value of a variable in a
// time slot corresponding to time greater than 0 is the value of this variable
// in the Preponed region of this time slot", and at time 0 it is the variable's
// default sampled value. §16.5.2 says why a live read will not do: "In an
// assertion, the sampled value is the only valid value of a variable during a
// clock tick", so `cond = 1; clk = 1;` and `clk = 1; cond = 1;` reach one
// verdict rather than two.
//
// Nothing writes into a Preponed region to fill this. §4.4.2.1 supplies the
// equivalence that makes it unnecessary -- "Sampling in the Preponed region is
// equivalent to sampling in the previous Postponed region" -- so Refill runs at
// the end of a time slot and what it copies there is the next slot's Preponed
// value.
//
// Only the variables an enrolled assertion reads are held, and a variable
// nothing enrolled reads back as absent so its caller keeps the live value.
class AssertionSampleStore {
 public:
  // Enrols `var`, whose value at the moment of the call is taken as its default
  // sampled value: §16.5.1 makes that "the value assigned in its declaration,
  // or, in the absence of such an assignment, ... the default (or
  // uninitialized) value of the corresponding type", which is what a variable
  // holds after its declaration is lowered and before any process has run.
  // Enrolling the same variable twice keeps the first default.
  void Register(const Variable* var, Arena& arena);

  // Copies every enrolled variable's value. Call at the end of a time slot,
  // where §4.4.2.1 makes the copy the next slot's Preponed value.
  void Refill(Arena& arena);

  // §16.5.1's sampled value of `var` in the time slot at `t`, or nullptr where
  // `var` was never enrolled.
  const Logic4Vec* Read(const Variable* var, SimTime t) const;

  // The same value where a concurrent assertion's property is what is being
  // evaluated, and nullptr everywhere else. This is the whole of the §16.5.1
  // rule a variable read asks about, so a reader consults it and keeps the live
  // value whenever it answers nothing.
  const Logic4Vec* ReadWithinProperty(const Variable* var, SimTime t) const {
    return evaluating_property_ ? Read(var, t) : nullptr;
  }

  // §16.5.1 applies to the expressions of a concurrent assertion and to nothing
  // else in the same source, so a read answers a sampled value only while such
  // an assertion's property is being evaluated. An action block's own
  // statements, and every procedure around the assertion, read live values.
  void SetEvaluatingProperty(bool on) { evaluating_property_ = on; }
  bool EvaluatingProperty() const { return evaluating_property_; }

 private:
  struct Entry {
    Logic4Vec default_value;
    Logic4Vec preponed_value;
  };

  std::unordered_map<const Variable*, Entry> entries_;
  bool evaluating_property_ = false;
};

}  // namespace delta

#endif  // DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_
