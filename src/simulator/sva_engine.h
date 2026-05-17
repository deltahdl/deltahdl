#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/types.h"

namespace delta {

class Scheduler;

// =============================================================================
// Assertion severity (section 16.3)
// =============================================================================

enum class AssertionSeverity : uint8_t {
  kInfo = 0,
  kWarning = 1,
  kError = 2,
  kFatal = 3,
};

std::string_view SeverityToString(AssertionSeverity sev);

// =============================================================================
// Property evaluation result
// =============================================================================

enum class PropertyResult : uint8_t {
  kPass,
  kFail,
  kVacuousPass,
  kPending,  // For non-overlapping implication awaiting next cycle.
};

// =============================================================================
// SequenceAttempt: tracks in-progress sequence match (section 16.9)
// =============================================================================

struct SequenceAttempt {
  uint32_t position = 0;
  uint32_t delay_remaining = 0;
  uint32_t match_count = 0;
  bool completed = false;
  bool failed = false;
};

void AdvanceSequence(SequenceAttempt& sa);

// =============================================================================
// SvaSequence: describes a sequence pattern
// =============================================================================

enum class SvaSequenceKind : uint8_t {
  kDelay,
  kConsecutiveRepetition,
  kGotoRepetition,
  kNonConsecutiveRepetition,
};

struct SvaSequence {
  SvaSequenceKind kind = SvaSequenceKind::kDelay;
  uint32_t delay_cycles = 0;
  uint32_t rep_min = 0;
  uint32_t rep_max = 0;
  std::function<bool(uint64_t)> expr_check;
};

// Sequence matching functions.
bool MatchRepetition(const SvaSequence& seq, const std::vector<uint64_t>& vals);
bool MatchGotoRepetition(const SvaSequence& seq,
                         const std::vector<uint64_t>& vals);
bool MatchNonConsecutiveRepetition(const SvaSequence& seq,
                                   const std::vector<uint64_t>& vals);
bool MatchDelaySequence(const SvaSequence& seq,
                        const std::vector<uint64_t>& vals);

// =============================================================================
// Sequence operators (section 16.9.6-9)
// =============================================================================

bool EvalSequenceAnd(bool a_match, bool b_match);
bool EvalSequenceOr(bool a_match, bool b_match);
bool EvalSequenceIntersect(bool a_match, bool b_match, uint32_t a_len,
                           uint32_t b_len);
bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values);

// =============================================================================
// Property evaluation (section 16.12)
// =============================================================================

PropertyResult EvalImplication(bool antecedent, bool consequent,
                               bool non_overlapping);
PropertyResult EvalPropertyNot(PropertyResult inner);
PropertyResult EvalPropertyAnd(PropertyResult a, PropertyResult b);
PropertyResult EvalPropertyOr(PropertyResult a, PropertyResult b);
PropertyResult EvalWithDisableIff(bool disable_cond, PropertyResult inner);
PropertyResult ResolveNonOverlapping(bool consequent_matched);

// =============================================================================
// AssertionKind: the four assertion statement kinds (§16.2)
// =============================================================================
//
// §16.2: "An assertion appears as an assertion statement that states the
// verification function to be performed.  The statement shall be of one of
// the following kinds: assert, assume, cover, restrict."  §16.2 also states
// that "There is no immediate restrict assertion statement", which is
// enforced by IsImmediateAssertionKindAllowed below.  The enum is reused by
// the §16.14.6 procedural-assertion queue so the kind survives the queueing
// step.

enum class AssertionKind : uint8_t {
  kAssert = 0,
  kAssume = 1,
  kCover = 2,
  kRestrict = 3,
};

bool IsImmediateAssertionKindAllowed(AssertionKind kind);

// =============================================================================
// AssertionTiming: the two timings (§16.2)
// =============================================================================
//
// §16.2: "There are two kinds of assertions: concurrent and immediate."
// The enum makes the §16.2 dichotomy explicit so callers can decide
// between the §16.3 (immediate) and §16.5/§16.14.6 (concurrent) code
// paths.

enum class AssertionTiming : uint8_t {
  kImmediate = 0,   // §16.3 — procedural event-semantics.
  kConcurrent = 1,  // §16.5 / §16.14.6 — clock-tick / sampled-value semantics.
};

// §16.2 P4: "Concurrent assertions are based on clock semantics and use
// sampled values of their expressions."  Returns true exactly when the
// timing classification implies §16.5.1 sampled-value semantics.
bool ConcurrentTimingUsesSampledValues(AssertionTiming timing);

// =============================================================================
// SampledValue: a sampled expression value (§16.5.1)
// =============================================================================
//
// §16.5.1 defines the *sampled value* concept used by concurrent assertions
// (and other constructs).  The default rule is "the sampled value of an
// expression is its value in the Preponed region".  The exception used by
// §16.14.6 is that "sampled values of automatic variables ... and local
// variables ... are their current values"; the kCurrent mode encodes that
// override.  kDefault models the time-0 fallback to the type's default
// value.

enum class SampleMode : uint8_t {
  kPreponed = 0,  // §16.5.1: value in the Preponed region of this time slot.
  kCurrent = 1,   // §16.5.1: automatic/local/active-free-checker exception.
  kDefault = 2,   // §16.5.1: time-0 fallback / type default.
};

struct SampledValue {
  uint64_t value = 0;
  SampleMode mode = SampleMode::kPreponed;
};

// §16.5.1: sampled value of a variable in a time slot > 0 is its value in
// the Preponed region; in a time slot = 0 it is the default sampled value.
SampledValue SampleStaticVariable(uint64_t preponed_value, SimTime t,
                                  uint64_t type_default);

// §16.5.1: sampled values of automatic / local / active-free-checker
// variables are their current values.  This is the exception used by
// §16.14.6 when capturing arguments of a procedural concurrent assertion.
SampledValue SampleAutomaticVariable(uint64_t current_value);

// §16.5.1: the default sampled value of the `triggered` event method and
// the sequence methods `triggered` and `matched` is false (1'b0).
SampledValue DefaultSampledValueOfTriggered();
SampledValue DefaultSampledValueOfMatched();

// §16.5.1: "The sampled value of an expression consisting of a single
// variable is the sampled value of this variable."  This wrapper is
// degenerate by design — it forwards the variable's SampledValue
// unchanged — but anchors N11 in the test surface.
SampledValue SampleSingleVariableExpression(SampledValue var_sample);

// §16.5.1: "The sampled value of a `const` cast expression (see 6.24.1
// and 16.14.6) is defined as the current value of its argument.  For
// example, if a is a variable, then the sampled value of const'(a) is
// the current value of a."  The result therefore carries kCurrent mode.
SampledValue SampleConstCastExpression(uint64_t argument_current_value);

// §16.5.1: "The sampled value of the `triggered` event method and the
// sequence methods `triggered` and `matched` (see 16.13.6) is defined as
// the current value returned by the event property or sequence method."
// Carries kCurrent mode for the same reason as SampleConstCastExpression.
SampledValue SampledValueOfTriggered(bool current_returned);
SampledValue SampledValueOfMatched(bool current_returned);

// §16.5.1: "The sampled value of any other expression is defined
// recursively using the values of its arguments.  For example, the
// sampled value of an expression e1 & e2 ... is the bitwise AND of the
// sampled values of e1 and e2."  Two-argument recursive sampler with a
// generic combinator covers the recursive case for the test surface.
SampledValue SampleRecursiveExpression(
    SampledValue a, SampledValue b,
    uint64_t (*combinator)(uint64_t, uint64_t));

// §16.5.1: "The default sampled value of any other variable or net is
// the default value of the corresponding type."  Like the static-
// variable case but without the declared-init fallback — the type
// default is the only value the rule considers.
SampledValue DefaultSampledValueOfVariableOrNet(uint64_t type_default);

// §16.5.1: "If a variable is an input variable of a clocking block, the
// variable shall be sampled by the clocking block with #1step sampling.
// Any other type of sampling for the clocking block variable shall
// result in an error."  Returns true iff the requested skew is #1step
// (modelled as the sentinel kStep1, since #1step is conceptually one
// simulation step before the clock tick, not a numeric delay).

enum class ClockingInputSkew : uint8_t {
  kStep1 = 0,    // §16.5.1: the only valid sampling for clocking-block inputs.
  kOther = 1,    // Any numeric or zero skew that is not #1step.
};

bool IsClockingBlockInputSamplingValid(ClockingInputSkew skew);

// =============================================================================
// DeferredAssertion: queued for Observed region (section 16.4)
// =============================================================================

struct DeferredAssertion {
  uint64_t condition_val = 0;
  std::string instance_name;
  std::function<void()> pass_action;
  std::function<void()> fail_action;
  AssertionSeverity severity = AssertionSeverity::kError;
  // §16.2: classification carried through the deferred queue so that the
  // §16.2 "no immediate restrict" rule can be enforced where this struct is
  // built and consumed.
  AssertionKind kind = AssertionKind::kAssert;
};

void ExecuteDeferredAssertionAction(const DeferredAssertion& da);

// =============================================================================
// ProceduralAssertionQueue: pending procedural concurrent assertions
// (§16.14.6)
// =============================================================================
//
// §16.14.6: a procedural concurrent assertion is not immediately evaluated;
// "the assertion and the current values of all constant and automatic
// expressions appearing in its assertion arguments ... are placed in a
// procedural assertion queue associated with the currently executing
// process."  Each queue entry is a *pending procedural assertion instance*.
// In the Observed region each pending instance shall *mature*, which means
// it is confirmed for execution.  A *procedural assertion flush point*
// clears the queue; "any currently pending procedural assertion instances
// will not mature, unless again placed on the queue."

struct PendingProceduralAssertion {
  AssertionKind kind = AssertionKind::kAssert;  // §16.2 kind carried through.
  std::string instance_name;
  // §16.14.6 P3: "current values of all constant and automatic expressions"
  // — these are captured using SampleAutomaticVariable / kCurrent per
  // §16.5.1.
  std::vector<SampledValue> sampled_args;
  bool matured = false;
};

class ProceduralAssertionQueue {
 public:
  void Enqueue(PendingProceduralAssertion pending);
  // §16.14.6: in the Observed region, mark every pending instance matured.
  void MatureAll();
  // §16.14.6: procedural assertion flush point clears the queue.
  void Flush();
  uint32_t Size() const;
  uint32_t MaturedCount() const;
  const std::vector<PendingProceduralAssertion>& Entries() const {
    return queue_;
  }

 private:
  std::vector<PendingProceduralAssertion> queue_;
};

// §16.14.6 P5: "A concurrent assertion statement that appears outside
// procedural code is referred to as a *static concurrent assertion
// statement*."  The predicate makes the parser/elaborator decision
// explicit so other stages can route static-vs-procedural traffic.
bool IsStaticConcurrentAssertion(bool appears_in_procedural_code);

// §16.14.6: "It shall be illegal to use automatic variables in clocking
// events."  Returns true exactly when the variable carrying the
// clocking event is non-automatic — anything else is the §16.14.6
// illegality the elaborator should reject.
bool IsAutomaticAllowedInClockingEvent(bool variable_is_automatic);

// §16.14.6: "If no clocking event is specified in a procedural
// concurrent assertion, the leading clocking event of the assertion
// shall be inferred from the procedural context, if possible.  If no
// clock can be inferred from the procedural context, then the clocks
// shall be inferred from the default clocking (see 14.12), as if the
// assertion were instantiated immediately before the procedure."
// The kind captures where the clock came from, or that no clock could
// be inferred (a downstream error).

enum class InferredClockKind : uint8_t {
  kFromProceduralContext = 0,
  kFromDefaultClocking = 1,
  kNotInferrable = 2,
};

struct InferredClock {
  InferredClockKind kind = InferredClockKind::kNotInferrable;
  std::string_view signal_name;
};

// Resolve the §16.14.6 clock-inference priority.  *proc_context_clock*
// is non-empty when the procedural context supplies a clock (per the
// rules below); *default_clock* is non-empty when a `default clocking`
// declaration is in scope.  Procedural context wins; default clocking
// is the fallback; if both are empty the result is kNotInferrable.
InferredClock InferClockForProceduralConcurrentAssertion(
    std::string_view proc_context_clock,
    std::string_view default_clock);

// §16.14.6: "A clock shall be inferred for the context of an always or
// initial procedure that satisfies the following requirements:
//   a) There is no blocking timing control in the procedure.
//   b) There is exactly one event control in the procedure.
//   c) One and only one event expression within the event control of
//      the procedure satisfies both of the following conditions: ..."
// The predicate is true exactly when all three requirements hold.
bool SatisfiesClockInferenceRequirements(bool no_blocking_timing_control,
                                          bool exactly_one_event_control,
                                          bool unique_qualifying_event_expr);

// §16.14.6: when a pending procedural assertion instance matures but its
// leading clocking event has not occurred in the current time step, the
// matured instance "shall be placed on the matured assertion queue, which
// will cause the assertion to begin an evaluation attempt upon the next
// clocking event that corresponds to the leading clocking event of the
// assertion."  The MaturedAssertionQueue models that holding area.

class MaturedAssertionQueue {
 public:
  void Place(PendingProceduralAssertion matured);
  // Drain everything queued for the next clock-tick evaluation attempt.
  std::vector<PendingProceduralAssertion> TakeAll();
  uint32_t Size() const;

 private:
  std::vector<PendingProceduralAssertion> queue_;
};

// =============================================================================
// AssertionControl: per-instance assertion control (section 16.13)
// =============================================================================

class AssertionControl {
 public:
  bool IsEnabled(std::string_view inst) const;
  void SetOff(std::string_view inst);
  void SetOn(std::string_view inst);
  void Kill(std::string_view inst);
  bool WasKilled(std::string_view inst) const;

  void SetGlobalOff();
  void SetGlobalOn();

  bool IsPassEnabled(std::string_view inst) const;
  void SetPassOff(std::string_view inst);

  bool IsFailEnabled(std::string_view inst) const;
  void SetFailOff(std::string_view inst);
  void SetFailOn(std::string_view inst);

 private:
  bool global_off_ = false;
  std::unordered_set<std::string> disabled_;
  std::unordered_set<std::string> killed_;
  std::unordered_set<std::string> pass_off_;
  std::unordered_set<std::string> fail_off_;
};

// =============================================================================
// SvaEngine: top-level SVA engine (section 16)
// =============================================================================

class SvaEngine {
 public:
  void QueueDeferredAssertion(const DeferredAssertion& da);
  void QueueDeferredAssertionIfEnabled(const DeferredAssertion& da);
  void FlushDeferredAssertions(Scheduler& sched, SimTime time);
  void FlushDeferredAssertionsRespectingControl(Scheduler& sched, SimTime time);
  void KillAssertionsForInstance(std::string_view inst);

  uint32_t DeferredQueueSize() const;
  AssertionControl& GetControl() { return control_; }

  // §16.14.6: every executing process owns its own procedural assertion
  // queue.  The engine exposes one named queue per process identifier so
  // §16.14.6 P3 ("a procedural assertion queue associated with the
  // currently executing process") can be modelled.
  ProceduralAssertionQueue& GetProceduralQueue(std::string_view process_id);

 private:
  std::vector<DeferredAssertion> deferred_queue_;
  AssertionControl control_;
  std::unordered_map<std::string, ProceduralAssertionQueue> procedural_queues_;
};

}  // namespace delta
