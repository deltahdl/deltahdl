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
bool EvalSequenceOr(bool a_match, bool b_match);
bool EvalSequenceIntersect(bool a_match, bool b_match, uint32_t a_len,
                           uint32_t b_len);
bool EvalThroughout(const std::function<bool(uint64_t)>& check,
                    const std::vector<uint64_t>& values);

PropertyResult EvalImplication(bool antecedent, bool consequent,
                               bool non_overlapping);
PropertyResult EvalPropertyNot(PropertyResult inner);
PropertyResult EvalPropertyAnd(PropertyResult a, PropertyResult b);
PropertyResult EvalPropertyOr(PropertyResult a, PropertyResult b);
PropertyResult EvalWithDisableIff(bool disable_cond, PropertyResult inner);
PropertyResult ResolveNonOverlapping(bool consequent_matched);

enum class AssertionKind : uint8_t {
  kAssert = 0,
  kAssume = 1,
  kCover = 2,
  kRestrict = 3,
};

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
  uint32_t Size() const;
  uint32_t MaturedCount() const;
  uint32_t NonMaturedCount() const;
  const std::vector<PendingDeferredReport>& Entries() const { return entries_; }

 private:
  std::vector<PendingDeferredReport> entries_;
};

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
  uint32_t Size() const;
  uint32_t MaturedCount() const;
  const std::vector<PendingProceduralAssertion>& Entries() const {
    return queue_;
  }

 private:
  std::vector<PendingProceduralAssertion> queue_;
};

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
