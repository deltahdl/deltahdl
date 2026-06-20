#ifndef DELTA_SIMULATOR_SVA_ENGINE_QUEUES_H_
#define DELTA_SIMULATOR_SVA_ENGINE_QUEUES_H_

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/types.h"
#include "simulator/sva_engine_properties.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/sva_engine_sequences.h"

namespace delta {

class Scheduler;

struct DeferredAssertion {
  uint64_t condition_val = 0;
  std::string instance_name;
  std::function<void()> pass_action;
  std::function<void()> fail_action;
  AssertionSeverity severity = AssertionSeverity::kError;

  AssertionKind kind = AssertionKind::kAssert;

  bool has_else_clause = true;
};

void ExecuteDeferredAssertionAction(const DeferredAssertion& da);

bool UsesErrorSeverityFallback(const DeferredAssertion& da);

enum class DeferralKind : uint8_t {
  kObserved = 0,
  kFinal = 1,
};

enum class FlushPointReason : uint8_t {
  kNone = 0,
  kEventControlResume = 1,
  kWaitResume = 2,
  kAlwaysCombSignalDelta = 3,
  kAlwaysLatchSignalDelta = 4,
  kDisableOuterScope = 5,
};

bool IsDeferredFlushPoint(FlushPointReason reason);

struct PendingDeferredReport {
  std::string process_id;
  DeferralKind deferral = DeferralKind::kObserved;
  DeferredAssertion da;
  bool matured = false;
};

class DeferredReportQueue {
 public:
  void Enqueue(PendingDeferredReport report);
  void MatureObservedReports();
  void MatureFinalReports();
  std::vector<PendingDeferredReport> TakeMaturedObserved();
  std::vector<PendingDeferredReport> TakeMaturedFinal();
  void FlushNonMatured();

  // §16.4.4: disabling one specific deferred assertion cancels that
  // assertion's still-pending reports while leaving every other assertion's
  // pending reports, and any already-matured report of the named assertion, in
  // place.
  void FlushNonMaturedForInstance(std::string_view instance_name);
  uint32_t Size() const;
  uint32_t MaturedCount() const;
  uint32_t NonMaturedCount() const;
  const std::vector<PendingDeferredReport>& Entries() const { return entries_; }

 private:
  std::vector<PendingDeferredReport> entries_;
};

// §16.14.6.2: a process reaches a procedural assertion flush point when it
// resumes after suspending at an event control or wait, when an always_comb or
// always_latch process re-runs due to a dependent-signal transition, or when
// its outermost scope is disabled. Reaching such a point flushes the pending
// procedural concurrent assertion instances of that process. The flush-point
// conditions coincide with the deferred case, so the FlushPointReason values
// are shared; this predicate is the procedural-concurrent-assertion view of
// that classification.
bool IsProceduralAssertionFlushPoint(FlushPointReason reason);

struct PendingProceduralAssertion {
  AssertionKind kind = AssertionKind::kAssert;
  std::string instance_name;

  std::vector<SampledValue> sampled_args;
  bool matured = false;
};

class ProceduralAssertionQueue {
 public:
  void Enqueue(PendingProceduralAssertion pending);

  void MatureAll();

  void Flush();

  // §16.14.6.2: at a flush point only the instances that have not yet matured
  // are discarded; instances that already matured stay queued so they can
  // still proceed to evaluation.
  void FlushPending();

  // §16.14.6.4: disabling one specific procedural concurrent assertion clears
  // that assertion's still-pending instances from the queue while leaving every
  // other assertion's pending instances, and any already-matured instance of
  // the named assertion, in place.
  void FlushPendingForInstance(std::string_view instance_name);
  uint32_t Size() const;
  uint32_t MaturedCount() const;
  const std::vector<PendingProceduralAssertion>& Entries() const {
    return queue_;
  }

 private:
  std::vector<PendingProceduralAssertion> queue_;
};

// §16.14.6.4: a `disable` statement may name several kinds of object; which one
// it targets decides whether the addressed process's pending procedural
// concurrent assertion instances are flushed.
enum class DisableTarget : uint8_t {
  kSpecificAssertion = 0,
  kOutermostScope = 1,
  kNonOutermostScope = 2,
  kTask = 3,
};

// §16.14.6.4: disabling a specific procedural concurrent assertion, or the
// outermost scope of a procedure that has a pending procedural assertion queue,
// flushes pending procedural assertion instances; disabling a task or a
// non-outermost scope of a procedure does not.
bool DisableFlushesProceduralAssertions(DisableTarget target);

// §16.4.4: disabling a specific deferred assertion, or the outermost scope of a
// procedure that has an active deferred assertion report queue, clears pending
// reports; disabling a task or a non-outermost scope of a procedure does not.
bool DisableFlushesDeferredAssertions(DisableTarget target);

bool IsStaticConcurrentAssertion(bool appears_in_procedural_code);

bool IsAutomaticAllowedInClockingEvent(bool variable_is_automatic);

enum class InferredClockKind : uint8_t {
  kFromProceduralContext = 0,
  kFromDefaultClocking = 1,
  kNotInferrable = 2,
};

struct InferredClock {
  InferredClockKind kind = InferredClockKind::kNotInferrable;
  std::string_view signal_name;
};

InferredClock InferClockForProceduralConcurrentAssertion(
    std::string_view proc_context_clock, std::string_view default_clock);

bool SatisfiesClockInferenceRequirements(bool no_blocking_timing_control,
                                         bool exactly_one_event_control,
                                         bool unique_qualifying_event_expr);

class MaturedAssertionQueue {
 public:
  void Place(PendingProceduralAssertion matured);

  std::vector<PendingProceduralAssertion> TakeAll();
  uint32_t Size() const;

 private:
  std::vector<PendingProceduralAssertion> queue_;
};

// §16.14.1: which branch of an assert statement's action_block runs after the
// property is evaluated. When the property holds, the pass statements run; when
// it fails, the fail statements run; when the property is disabled (e.g. by a
// `disable iff`), no action_block statement runs at all.
enum class AssertActionBlockChoice : uint8_t {
  kPass,
  kFail,
  kNone,
};

// §16.14.1: choose the action_block branch for an assert statement from the
// outcome of evaluating its property. A disabled evaluation suppresses the
// action_block entirely and takes precedence over the pass/fail distinction.
AssertActionBlockChoice SelectAssertActionBlock(bool property_passed,
                                                bool property_disabled);

// §16.14.1: the execution of the pass and fail statements can be controlled
// using the assertion action control tasks (see §20.11). This composes the base
// §16.14.1 choice with the per-instance pass/fail enables maintained for the
// §20.11 control tasks: a pass branch is suppressed when the pass action is
// disabled, and a fail branch is suppressed when the fail action is disabled.
AssertActionBlockChoice ResolveAssertActionUnderControl(
    AssertActionBlockChoice base, bool pass_action_enabled,
    bool fail_action_enabled);

// §16.14.1: when the else clause is omitted, the tool calls $error on failure
// unless $assertcontrol has been used to suppress the failure (see §20.11).
// This is the §16.14.1 default-$error condition (UsesErrorSeverityFallback)
// gated by the §20.11 fail-action enable, so a FailOff control suppresses the
// otherwise-default $error.
bool CallsDefaultErrorOnFailure(const DeferredAssertion& da,
                                bool fail_action_enabled);

// §16.14.1: the conventions regarding default severity for a concurrent
// assertion action block are the same as for immediate assertions; the default
// severity is error.
AssertionSeverity DefaultConcurrentAssertActionSeverity();

// §16.14.1: the pass and fail statements of an assert statement are executed in
// the Reactive region.
Region ConcurrentAssertActionRegion();

// === §16.14.2 Assume statement ===

// §16.14.2: for simulation an assumed property is constrained to hold and, like
// an asserted property, is checked and reported when it fails. Its action_block
// branch follows the property outcome exactly as an assert statement's does: a
// true evaluation runs the pass statements, a false evaluation runs the fail
// statements, and a disabled evaluation runs neither. Delegating to the
// §16.14.1 selector keeps the assume and assert action-block behavior
// identical.
inline AssertActionBlockChoice SelectAssumeActionBlock(bool property_passed,
                                                       bool property_disabled) {
  return SelectAssertActionBlock(property_passed, property_disabled);
}

// §16.14.2: the pass and fail statements of an assume statement can be
// controlled with the §20.11 assertion action control tasks, the same way an
// assert statement's are.
inline AssertActionBlockChoice ResolveAssumeActionUnderControl(
    AssertActionBlockChoice base, bool pass_action_enabled,
    bool fail_action_enabled) {
  return ResolveAssertActionUnderControl(base, pass_action_enabled,
                                         fail_action_enabled);
}

// §16.14.2: an assume statement has a fail action — unlike a cover statement —
// so when its else clause is omitted the tool calls $error on a failing
// evaluation, unless a §20.11 control has disabled the fail action. A disabled
// evaluation is neither a pass nor a fail, so the caller passes
// property_failed=false for it and no default $error is issued.
inline bool AssumeCallsDefaultErrorOnFailure(bool property_failed,
                                             bool has_else_clause,
                                             bool fail_action_enabled) {
  return property_failed && !has_else_clause && fail_action_enabled;
}

// §16.14.2: the directive that an assertion-biasing dist (an
// `expression dist { dist_list }`, defined in A.1.10) appears in determines how
// the dist operator is interpreted for random simulation.
enum class BiasedAssertionDirective : uint8_t {
  kAssert,
  kAssume,
  kCover,
};

// §16.14.2: when a property that uses biasing appears in an assert or cover
// statement, the dist operator is equivalent to the inside operator and the
// weight specification is ignored. Only in an assume statement do the weights
// take effect, biasing the random selection of free-variable values.
inline bool BiasingWeightsIgnored(BiasedAssertionDirective directive) {
  return directive == BiasedAssertionDirective::kAssert ||
         directive == BiasedAssertionDirective::kCover;
}

// §16.14.2: within an assert or cover statement a biased dist behaves as the
// inside operator — plain set membership with the weights dropped. In an assume
// statement the weights are honored, so the dist is not reduced to inside
// there.
inline bool BiasedDistActsAsInside(BiasedAssertionDirective directive) {
  return BiasingWeightsIgnored(directive);
}

// §16.14.2: a property that is assumed shall hold in the same way with or
// without biasing. The set of free-variable values that satisfy an assumption
// is the membership set of the distribution and does not depend on the weights;
// biasing only chooses among those legal values when there is a choice at a
// given time. Whether `value` is a legal selection is therefore independent of
// whether biasing weights are present.
inline bool AssumeValueIsLegalUnderBiasing(int64_t value,
                                           const std::vector<int64_t>& members,
                                           bool /*weights_present*/) {
  for (int64_t member : members) {
    if (member == value) return true;
  }
  return false;
}

// §16.14.2: for an assume statement the biasing weights select among the legal
// free-variable values according to their cumulative distribution. Given the
// per-candidate weights and a random draw in [0, sum(weights)), return the
// index of the chosen candidate. (In an assert or cover statement the weights
// are ignored, so this weighted selection does not apply there.)
inline std::size_t SelectBiasedFreeVariable(
    const std::vector<uint32_t>& weights, uint64_t draw) {
  uint64_t cumulative = 0;
  for (std::size_t i = 0; i < weights.size(); ++i) {
    cumulative += weights[i];
    if (draw < cumulative) return i;
  }
  return weights.empty() ? 0 : weights.size() - 1;
}

// === §16.14.4 Restrict statement ===

// §16.14.4: a restrict property statement shares the constraining semantics of
// assume property — it directs the tool to take the property as holding and
// bounds the explored state space the same way — so for formal analysis the two
// behave identically.
bool RestrictSharesAssumeConstraintSemantics();

// §16.14.4: in contrast to assume property, a restrict property statement is
// not verified in simulation. No pass/fail evaluation runs for it, so it never
// yields a run-time pass or fail result the way an assumed or asserted property
// does.
bool RestrictIsVerifiedInSimulation();

// §16.14.4: because a restrict is not verified in simulation, a cycle in which
// its property does not hold (e.g. a restricted ctr taking value 1) is not
// flagged — violating the restriction during simulation is not an error.
bool RestrictViolationIsSimulationError();

// === §16.14.5 Using concurrent assertion statements outside procedural code
// ===

// §16.14.5: a concurrent assertion statement used outside procedural code (a
// static concurrent assertion) follows `always` semantics — a new evaluation
// attempt of the underlying property_spec begins at every occurrence of its
// leading clock event. Over a run with the given number of leading clock ticks,
// that many attempts are started, so the property is checked from the beginning
// to the end of simulation.
int StaticConcurrentAssertionAttemptsStarted(int leading_clock_ticks);

// §16.14.5: an `assert property (ps) action_block` written outside procedural
// code is equivalent to `always assert property (ps) action_block;`.
bool StaticAssertEquivalentToAlwaysAssert();

// §16.14.5: a `cover property (ps) statement_or_null` written outside
// procedural code is equivalent to `always cover property (ps)
// statement_or_null`.
bool StaticCoverEquivalentToAlwaysCover();

// §16.9.4: the global clocking past value-change functions compare the sampled
// value at the global clock tick that immediately precedes the current tick
// with the value at the current tick. $rose_gclk reports the LSB changing to 1,
// $fell_gclk the LSB changing to 0, $stable_gclk the whole expression being
// unchanged, and $changed_gclk the whole expression having changed.
bool RoseGclk(uint64_t prev_lsb, uint64_t cur_lsb);
bool FellGclk(uint64_t prev_lsb, uint64_t cur_lsb);
bool StableGclk(uint64_t prev_value, uint64_t cur_value);
bool ChangedGclk(uint64_t prev_value, uint64_t cur_value);

// §16.9.4: the global clocking future value-change functions are the same
// except that they use the subsequent value of the expression, sampled at the
// next global clock tick. $rising_gclk reports the LSB changing to 1 and
// $falling_gclk the LSB changing to 0 at the next global clock tick;
// $steady_gclk reports the expression not changing at the next tick; and
// $changing_gclk is the complement of $steady_gclk.
bool RisingGclk(uint64_t cur_lsb, uint64_t next_lsb);
bool FallingGclk(uint64_t cur_lsb, uint64_t next_lsb);
bool SteadyGclk(uint64_t cur_value, uint64_t next_value);
bool ChangingGclk(uint64_t cur_value, uint64_t next_value);

// §16.9.4: execution of the action block of an assertion containing global
// clocking future sampled value functions is delayed until the global clock
// tick that follows the last tick of the assertion clock for the attempt. When
// the attempt fails and $error is called by default (see §16.14.1), that $error
// is likewise issued at that following global clock tick rather than at the
// last assertion-clock tick.
bool GclkFutureActionBlockDelayedToFollowingGlobalTick();

// §16.9.4: the behavior of asynchronous controls such as $assertcontrol (see
// §20.11) is with respect to the interval of the evaluation attempt, whose end
// is the last tick of the assertion clock. A $assertcontrol Kill (control_type
// 5) executed in a time step strictly after that last tick does not affect the
// attempt, even if it runs no later than the following global clock tick. The
// parameter is true when the Kill occurs at or before the last assertion-clock
// tick.
bool GclkFutureKillAffectsAttempt(bool kill_at_or_before_last_assertion_tick);

// §20.11: the integer control_type argument selects the effect of the
// $assertcontrol system task. The values are those of Table 20-5.
enum class AssertControlType : uint8_t {
  kLock = 1,
  kUnlock = 2,
  kOn = 3,
  kOff = 4,
  kKill = 5,
  kPassOn = 6,
  kPassOff = 7,
  kFailOn = 8,
  kFailOff = 9,
  kNonvacuousOn = 10,
  kVacuousOff = 11,
};

// §20.11: when assertion_type is not specified it defaults to 255, so the task
// applies to all assertion types, expect statements, and violation reports. The
// bit values are those of Table 20-6.
inline constexpr uint32_t kAssertionTypeDefault = 255;

// §20.11: when directive_type is not specified it defaults to 7
// (Assert|Cover|Assume), so the task applies to all directive types. The bit
// values are those of Table 20-7.
inline constexpr uint32_t kDirectiveTypeDefault = 7;

// §20.11: Table 20-6 assertion_type bit values. A $assertcontrol assertion_type
// argument is an OR of these, selecting which assertion and report kinds the
// task affects.
enum class AssertionTypeBit : uint32_t {
  kConcurrent = 1,
  kSimpleImmediate = 2,
  kObservedDeferredImmediate = 4,
  kFinalDeferredImmediate = 8,
  kExpect = 16,
  kUnique = 32,
  kUnique0 = 64,
  kPriority = 128,
};

// §20.11: Table 20-7 directive_type bit values. A $assertcontrol directive_type
// argument is an OR of these, selecting which directive kinds the task affects.
enum class DirectiveTypeBit : uint32_t {
  kAssert = 1,
  kCover = 2,
  kAssume = 4,
};

// §20.11: the assertion_type argument selects assertion/report kinds by OR-ing
// Table 20-6 values; a task affects an assertion when that assertion's type bit
// is set in the mask. For example, mask 3 (Concurrent|SimpleImmediate) affects
// concurrent and simple immediate assertions but not deferred ones.
bool ControlAffectsAssertionType(uint32_t assertion_type_mask,
                                 AssertionTypeBit bit);

// §20.11: the directive_type argument selects directive kinds by OR-ing Table
// 20-7 values; a task affects a directive when that directive's bit is set in
// the mask. For example, mask 3 (Assert|Cover) affects assert and cover
// directives but not assume directives.
bool ControlAffectsDirectiveType(uint32_t directive_type_mask,
                                 DirectiveTypeBit bit);

// §20.11: the assertion action control tasks, and $assertcontrol with a
// control_type from 6 (PassOn) through 11 (VacuousOff), do not affect the
// statistics counters for the assertions; the status controls 1 (Lock) through
// 5 (Kill) do.
bool ControlTypeAffectsStatistics(int control_type);

// §20.11: the convenience and backward-compatibility tasks are defined in terms
// of $assertcontrol. This records the equivalent control_type, assertion_type,
// and directive_type a named task expands to.
struct AssertControlInvocation {
  uint32_t control_type = 0;
  uint32_t assertion_type = 0;
  uint32_t directive_type = 0;
};

// §20.11: expand a convenience assertion control task name (with the leading
// '$') to its equivalent $assertcontrol invocation. The $asserton/$assertoff/
// $assertkill tasks expand with assertion_type 15 and the action control tasks
// with assertion_type 31; both use directive_type 7. Returns false for a name
// that is not one of the convenience tasks.
bool EquivalentAssertControlForTask(std::string_view task_name,
                                    AssertControlInvocation& out);

class AssertionControl {
 public:
  bool IsEnabled(std::string_view inst) const;
  void SetOff(std::string_view inst);
  void SetOn(std::string_view inst);
  void Kill(std::string_view inst);
  bool WasKilled(std::string_view inst) const;

  void SetGlobalOff();
  void SetGlobalOn();

  // §20.11: Lock (control_type 1) prevents any status change of the named
  // assertion until it is unlocked; while locked, no $assertcontrol affects it.
  // Unlock (control_type 2) removes the locked status.
  void Lock(std::string_view inst);
  void Unlock(std::string_view inst);
  bool IsLocked(std::string_view inst) const;

  bool IsPassEnabled(std::string_view inst) const;
  void SetPassOff(std::string_view inst);
  // §20.11: PassOn (control_type 6) re-enables the pass action for both vacuous
  // and nonvacuous success.
  void SetPassOn(std::string_view inst);

  // §20.11: NonvacuousOn (control_type 10) enables the pass action on
  // nonvacuous success; VacuousOff (control_type 11) stops the pass action on
  // vacuous success. Pass enablement is therefore tracked per success kind.
  bool IsVacuousPassEnabled(std::string_view inst) const;
  bool IsNonvacuousPassEnabled(std::string_view inst) const;
  void SetNonvacuousOn(std::string_view inst);
  void SetVacuousOff(std::string_view inst);

  bool IsFailEnabled(std::string_view inst) const;
  void SetFailOff(std::string_view inst);
  void SetFailOn(std::string_view inst);

  // §20.11: apply a $assertcontrol invocation by its integer control_type to
  // the named assertion. A locked assertion is unaffected by any control_type
  // other than Unlock.
  void ApplyControl(int control_type, std::string_view inst);

 private:
  bool global_off_ = false;
  std::unordered_set<std::string> disabled_;
  std::unordered_set<std::string> killed_;
  std::unordered_set<std::string> locked_;
  std::unordered_set<std::string> vacuous_pass_off_;
  std::unordered_set<std::string> nonvacuous_pass_off_;
  std::unordered_set<std::string> fail_off_;
};

// §16.17: the expect statement is a blocking statement that waits on a property
// evaluation. When activated it starts a single evaluation thread, and the
// outcome of that thread drives both whether the process keeps blocking and
// which arm of the action block runs. These pure helpers encode that behavior
// independent of the surrounding scheduling machinery.
enum class ExpectActionKind : uint8_t {
  kBlock,        // property still pending — the process stays blocked
  kRunPass,      // property succeeded — take the action block's pass arm
  kRunFail,      // property failed and an else clause is present
  kReportError,  // property failed with no else clause — call $error
};

// §16.17: map an expect property's evaluation outcome onto the action the
// expecting process takes. While the property is pending the process remains
// blocked. On success the optional pass statement runs. On failure the else
// clause runs when present; otherwise the tool reports the failure via $error
// (the $assertcontrol suppression of §20.11 is applied by that machinery).
ExpectActionKind ResolveExpectAction(PropertyResult result,
                                     bool has_else_clause);

// §16.17: the expecting process blocks until the property succeeds or fails,
// and is unblocked exactly when the evaluation resolves. While the result is
// pending it stays blocked and the single evaluation thread keeps running; once
// the property resolves it stops being evaluated.
bool ExpectProcessRemainsBlocked(PropertyResult result);

// §16.17: when executed, an expect statement starts its evaluation on the
// subsequent clocking event — the first evaluation takes place on the next
// clocking event, never on one coincident with the tick at which the expect
// was activated. Returns true for a clocking event strictly after that tick.
bool ExpectClockingEventBeginsEvaluation(uint64_t activation_tick,
                                         uint64_t clocking_event_tick);

// §16.17: the statement following the expect, and the action block, run after
// the Observed region in which the property completes its evaluation — i.e. in
// the Reactive region of that time step.
inline constexpr Region ExpectResumeRegion() { return Region::kReactive; }

// §16.17: when the else clause is omitted, the tool reports a failed expect by
// calling $error, i.e. at error severity.
inline constexpr AssertionSeverity ExpectDefaultFailSeverity() {
  return AssertionSeverity::kError;
}

class SvaEngine {
 public:
  void QueueDeferredAssertion(const DeferredAssertion& da);
  void QueueDeferredAssertionIfEnabled(const DeferredAssertion& da);
  void FlushDeferredAssertions(Scheduler& sched, SimTime time);
  void FlushDeferredAssertionsRespectingControl(Scheduler& sched, SimTime time);
  void KillAssertionsForInstance(std::string_view inst);

  uint32_t DeferredQueueSize() const;
  AssertionControl& GetControl() { return control_; }

  ProceduralAssertionQueue& GetProceduralQueue(std::string_view process_id);

  void QueuePendingReport(std::string_view process_id,
                          const DeferredAssertion& da, DeferralKind kind);

  void MatureObservedReports(std::string_view process_id);
  void MatureFinalReports(std::string_view process_id);

  uint32_t ExecuteMaturedObservedInReactive(std::string_view process_id,
                                            Scheduler& sched, SimTime time);
  uint32_t ExecuteMaturedFinalInPostponed(std::string_view process_id,
                                          Scheduler& sched, SimTime time);

  void OnDeferredFlushPoint(std::string_view process_id,
                            FlushPointReason reason);

  void OnProceduralAssertionFlushPoint(std::string_view process_id,
                                       FlushPointReason reason);

  // §16.14.6.4: apply a `disable` statement's effect on a process's pending
  // procedural concurrent assertion queue. Disabling the named specific
  // assertion clears only that assertion's pending instances; disabling the
  // outermost scope flushes the whole pending queue; disabling a task or a
  // non-outermost scope leaves the queue untouched. Already-matured attempts
  // are never affected. The normal disable activities of §9.6.2 happen
  // elsewhere, in addition to this queue effect.
  void ApplyDisableToProceduralAssertions(std::string_view process_id,
                                          DisableTarget target,
                                          std::string_view assertion_instance);

  // §16.4.4: apply a `disable` statement's effect on a process's deferred
  // assertion report queue. Disabling the named specific deferred assertion
  // cancels only that assertion's pending reports; disabling the outermost
  // scope clears all pending reports on the queue; disabling a task or a
  // non-outermost scope leaves the queue untouched. Already-matured reports are
  // never affected. The normal disable activities of §9.6.2 happen elsewhere,
  // in addition to this queue effect.
  void ApplyDisableToDeferredAssertions(std::string_view process_id,
                                        DisableTarget target,
                                        std::string_view assertion_instance);

  DeferredReportQueue& GetDeferredReportQueue(std::string_view process_id);
  const DeferredReportQueue* PeekDeferredReportQueue(
      std::string_view process_id) const;

 private:
  std::vector<DeferredAssertion> deferred_queue_;
  AssertionControl control_;
  std::unordered_map<std::string, ProceduralAssertionQueue> procedural_queues_;
  std::unordered_map<std::string, DeferredReportQueue> per_process_reports_;
};

}  // namespace delta

#endif  // DELTA_SIMULATOR_SVA_ENGINE_QUEUES_H_
