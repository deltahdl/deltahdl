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

enum class AssertionSeverity : uint8_t {
  kInfo = 0,
  kWarning = 1,
  kError = 2,
  kFatal = 3,
};

std::string_view SeverityToString(AssertionSeverity sev);

enum class PropertyResult : uint8_t {
  kPass,
  kFail,
  kVacuousPass,
  kPending,
};

struct SequenceAttempt {
  uint32_t position = 0;
  uint32_t delay_remaining = 0;
  uint32_t match_count = 0;
  bool completed = false;
  bool failed = false;
};

void AdvanceSequence(SequenceAttempt& sa);

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

bool MatchRepetition(const SvaSequence& seq, const std::vector<uint64_t>& vals);
bool MatchGotoRepetition(const SvaSequence& seq,
                         const std::vector<uint64_t>& vals);
bool MatchNonConsecutiveRepetition(const SvaSequence& seq,
                                   const std::vector<uint64_t>& vals);
bool MatchDelaySequence(const SvaSequence& seq,
                        const std::vector<uint64_t>& vals);

bool EvalSequenceAnd(bool a_match, bool b_match);

// §16.9.5: the composite `e1 and e2` requires both operands to match. The
// operands begin at the same time, but their matches can complete at different
// times; once one operand matches it waits for the other, so the composite
// match completes at the later of the two operand end times. This carries the
// end-time alongside the match decision that EvalSequenceAnd reports.
struct SequenceAndMatch {
  bool matched = false;
  uint32_t end_time = 0;
};
SequenceAndMatch EvalSequenceAndMatch(bool a_match, uint32_t a_end_time,
                                      bool b_match, uint32_t b_end_time);

bool EvalSequenceOr(bool a_match, bool b_match);
bool EvalSequenceIntersect(bool a_match, bool b_match, uint32_t a_len,
                           uint32_t b_len);
bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values);

// §16.12.7: an implication `sequence_expr |-> property_expr` (overlapped) or
// `sequence_expr |=> property_expr` (nonoverlapped) preconditions the consequent
// property_expr on a match of the antecedent sequence_expr. When the antecedent
// has no match the implication holds vacuously. The overlapped form evaluates
// the consequent at the end point of the match, so the result is the
// consequent's verdict; the nonoverlapped form starts the consequent one clock
// tick later, so its verdict is deferred (kPending) and settled by
// ResolveNonOverlapping — capturing `seq |=> p` ≡ `seq ##1 `true |-> p`.
PropertyResult EvalImplication(bool antecedent, bool consequent,
                               bool non_overlapping);

// §16.12.3: a negation `not property_expr` returns the opposite verdict of the
// underlying property_expr — a true underlying evaluation makes the negation
// false, and a false one makes it true. Each attempt of the negation drives a
// single attempt of the underlying property_expr.
PropertyResult EvalPropertyNot(PropertyResult inner);
PropertyResult EvalPropertyAnd(PropertyResult a, PropertyResult b);

// §16.12.4: a disjunction `property_expr1 or property_expr2` evaluates to true
// if, and only if, at least one of the two operand property expressions
// evaluates to true. A vacuous pass counts as the operand holding, so a single
// holding operand is enough to make the whole disjunction hold.
PropertyResult EvalPropertyOr(PropertyResult a, PropertyResult b);

// §16.12.6: an if-else property is governed by the guard expression. When the
// guard holds, the overall result is that of the then-branch. The single-branch
// form (no else) holds vacuously when the guard is false, since there is nothing
// to check; the two-branch form routes a false guard to the else-branch instead.
PropertyResult EvalPropertyIfElse(bool cond, PropertyResult then_result,
                                  bool has_else, PropertyResult else_result);
PropertyResult EvalWithDisableIff(bool disable_cond, PropertyResult inner);

// §16.12.7: settles a deferred nonoverlapped (|=>) implication once the clock
// reaches the tick after the antecedent match, where the consequent is finally
// evaluated.
PropertyResult ResolveNonOverlapping(bool consequent_matched);

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
};

struct SampledValue {
  uint64_t value = 0;
  SampleMode mode = SampleMode::kPreponed;
};

SampledValue SampleStaticVariable(uint64_t preponed_value, SimTime t,
                                  uint64_t type_default);

SampledValue SampleAutomaticVariable(uint64_t current_value);

SampledValue DefaultSampledValueOfTriggered();
SampledValue DefaultSampledValueOfMatched();

SampledValue SampleSingleVariableExpression(SampledValue var_sample);

SampledValue SampleConstCastExpression(uint64_t argument_current_value);

SampledValue SampleProceduralAssertionArgument(uint64_t current_value);

SampledValue ProceduralArgumentValueAfterMature(SampledValue captured,
                                                 uint64_t later_underlying_value);

enum class ProceduralExecutionEffect : uint8_t {
  kActivation = 0,
  kCompletion = 1,
};

bool ProceduralExecutionAffects(ProceduralExecutionEffect effect,
                                 bool already_matured);

SampledValue SampleProceduralAssertionActionBlockArgument(uint64_t current_value);

bool ActionBlockMayModifyArgument();

uint64_t ReadProceduralConditionalGuard(uint64_t current_value,
                                         uint64_t sampled_value);

SampledValue SampledValueOfTriggered(bool current_returned);
SampledValue SampledValueOfMatched(bool current_returned);

SampledValue SampleRecursiveExpression(
    SampledValue a, SampledValue b,
    uint64_t (*combinator)(uint64_t, uint64_t));

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
    std::string_view proc_context_clock,
    std::string_view default_clock);

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
                          const DeferredAssertion& da,
                          DeferralKind kind);

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

}
