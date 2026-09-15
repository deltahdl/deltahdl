#ifndef DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_
#define DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_

#include <cstddef>
#include <cstdint>
#include <functional>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "simulator/sva_engine_sequences.h"

namespace delta {

class Arena;
struct Expr;
struct QueueObject;
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
// One evaluation of a sampled value function call site as the store keys its
// history: the site's expression, the variant its select indices take (see
// PastValue), and the time step the evaluation stands in.
struct SampleSite {
  const Expr* site = nullptr;
  uint64_t variant = 0;
  uint64_t now = 0;
};

class AssertionSampleStore {
 public:
  // Enrols `var`, whose value at the moment of the call is taken as its default
  // sampled value: §16.5.1 makes that "the value assigned in its declaration,
  // or, in the absence of such an assignment, ... the default (or
  // uninitialized) value of the corresponding type", which is what a variable
  // holds after its declaration is lowered and before any process has run.
  // Enrolling the same variable twice keeps the first default.
  void Register(const Variable* var, Arena& arena);

  // §16.6: "Elements of dynamic arrays, queues, and associative arrays that
  // are sampled for assertion expression evaluation may get removed from the
  // array or the array may get resized before the assertion expression is
  // evaluated. These specific array elements sampled for assertion expression
  // evaluation shall continue to exist within the scope of the assertion until
  // the assertion expression evaluation completes." A queue a property reads
  // an element of is enrolled whole, its elements at the moment of the call
  // being their default sampled values, and Refill copies them as it copies
  // a variable's value, so a select made while the property is evaluated reads
  // the element the queue held in the Preponed region whatever the queue holds
  // now.
  void RegisterQueue(const QueueObject* queue, Arena& arena);

  // Copies every enrolled variable's value and every enrolled queue's
  // elements. Call at the end of a time slot, where §4.4.2.1 makes the copy
  // the next slot's Preponed value.
  void Refill(Arena& arena);

  // The elements §16.5.1 samples for `queue` in the time slot at `t` where a
  // concurrent assertion's property is what is being evaluated, and nullptr
  // everywhere else and for a queue no such property reads, so a select
  // consults it and reads the live elements whenever it answers nothing.
  const std::vector<Logic4Vec>* ReadQueueWithinProperty(
      const QueueObject* queue, SimTime t) const;

  // §16.5.1's sampled value of `var` in the time slot at `t`, or nullptr where
  // `var` was never enrolled.
  const Logic4Vec* Read(const Variable* var, SimTime t) const;

  // The same value where a concurrent assertion's property is what is being
  // evaluated, and nullptr everywhere else. This is the whole of the §16.5.1
  // rule a variable read asks about, so a reader consults it and keeps the live
  // value whenever it answers nothing.
  const Logic4Vec* ReadWithinProperty(const Variable* var, SimTime t) const {
    if (!evaluating_property_) return nullptr;
    if (!reading_defaults_) return Read(var, t);
    auto it = entries_.find(var);
    return it == entries_.end() ? nullptr : &it->second.default_value;
  }

  // §16.5.1 applies to the expressions of a concurrent assertion and to nothing
  // else in the same source, so a read answers a sampled value only while such
  // an assertion's property is being evaluated. An action block's own
  // statements, and every procedure around the assertion, read live values.
  void SetEvaluatingProperty(bool on) { evaluating_property_ = on; }
  bool EvaluatingProperty() const { return evaluating_property_; }

  // §16.9.3: "When these functions are called at or before the simulation time
  // step in which the first clocking event occurs, the results are computed by
  // comparing the sampled value of the expression with its default sampled
  // value." Raised around one evaluation of a value-change function's argument,
  // this makes every read answer that default, so the comparison is made on the
  // expression the source wrote rather than on one variable of it.
  void SetReadingDefaults(bool on) { reading_defaults_ = on; }

  // §16.9.3: the sampled value a sampled-value-function call site saw at the
  // clock ticks before this one, `ticks_back` of them ago, or nullptr where the
  // site has not been evaluated that many times yet. The key is the call site's
  // own expression node: it is unique to one position in the source and is
  // evaluated once per tick of the clock the function samples on, so the
  // sequence of values it has seen is "the sampled value of the expression from
  // the most recent strictly prior time step in which the clocking event
  // occurred" and the ticks before that.
  // A site evaluated several times at one tick with different operands --
  // §16.9.3's `$past(b[i])` in a for loop over i -- keeps one history per
  // `variant`, the value the site's select indices took, so each iteration
  // reads the past value of its own bit.
  //
  // The history is read against `now`, the current time step: a site recorded
  // at this step already holds this tick's sample as its most recent entry,
  // so `ticks_back` counts from behind it, and a site last recorded at an
  // earlier step counts from that entry itself.
  const Logic4Vec* PastValue(const SampleSite& site, uint32_t ticks_back) const;

  // Records what the site sampled at this tick, so the next evaluation of it
  // can read this value back. `depth` is how many ticks of history that site
  // asks for, which bounds what is kept. Recorded twice in one time step, a
  // site keeps one entry for it: §16.9.3 samples at the clock tick, so the
  // process a site stands in records every site as it resumes at its clock,
  // and the site's own evaluation, where the statement is reached, records
  // the same value over it.
  void RecordTick(const SampleSite& site, const Logic4Vec& sampled,
                  uint32_t depth, Arena& arena);

  // A copy of `sampled` that owns its words, for a caller that keeps a sampled
  // value past the tick it read it at: the value a read of a variable answers
  // shares the variable's words, and the tick history above is kept by copy
  // for the same reason. §16.9.4's attempts are the caller, each keeping what
  // its future call sites sampled at its own tick until the global clocking
  // tick that answers it.
  static Logic4Vec OwnedSample(const Logic4Vec& sampled, Arena& arena);

 private:
  struct Entry {
    Logic4Vec default_value;
    Logic4Vec preponed_value;
  };

  struct QueueEntry {
    std::vector<Logic4Vec> default_elements;
    std::vector<Logic4Vec> preponed_elements;
  };

  // One call site's history under one variant of its operands.
  struct SiteKey {
    const Expr* site;
    uint64_t variant;
    bool operator==(const SiteKey& other) const {
      return site == other.site && variant == other.variant;
    }
  };
  struct SiteKeyHash {
    size_t operator()(const SiteKey& key) const {
      return std::hash<const Expr*>()(key.site) ^
             (std::hash<uint64_t>()(key.variant) << 1);
    }
  };

  std::unordered_map<const Variable*, Entry> entries_;
  std::unordered_map<const QueueObject*, QueueEntry> queue_entries_;
  // Most recent first, so entry 0 is the previous tick's value -- $past's
  // default of one tick back.
  struct SiteHistory {
    // Most recent first.
    std::vector<Logic4Vec> values;
    // The time step the most recent entry was recorded at.
    uint64_t recorded_at = UINT64_MAX;
  };
  std::unordered_map<SiteKey, SiteHistory, SiteKeyHash> tick_history_;
  bool evaluating_property_ = false;
  bool reading_defaults_ = false;
};

}  // namespace delta

#endif  // DELTA_SIMULATOR_SVA_ENGINE_SAMPLING_H_
