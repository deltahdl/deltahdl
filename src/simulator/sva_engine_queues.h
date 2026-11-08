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

  void FlushNonMaturedForInstance(std::string_view instance_name);
  uint32_t Size() const;
  uint32_t MaturedCount() const;
  uint32_t NonMaturedCount() const;
  const std::vector<PendingDeferredReport>& Entries() const { return entries_; }

 private:
  std::vector<PendingDeferredReport> entries_;
};

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

  void FlushPending();

  void FlushPendingForInstance(std::string_view instance_name);
  uint32_t Size() const;
  uint32_t MaturedCount() const;
  const std::vector<PendingProceduralAssertion>& Entries() const {
    return queue_;
  }

 private:
  std::vector<PendingProceduralAssertion> queue_;
};

enum class DisableTarget : uint8_t {
  kSpecificAssertion = 0,
  kOutermostScope = 1,
  kNonOutermostScope = 2,
  kTask = 3,
};

bool DisableFlushesProceduralAssertions(DisableTarget target);

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

enum class AssertActionBlockChoice : uint8_t {
  kPass,
  kFail,
  kNone,
};

AssertActionBlockChoice SelectAssertActionBlock(bool property_passed,
                                                bool property_disabled);

AssertActionBlockChoice ResolveAssertActionUnderControl(
    AssertActionBlockChoice base, bool pass_action_enabled,
    bool fail_action_enabled);

bool CallsDefaultErrorOnFailure(const DeferredAssertion& da,
                                bool fail_action_enabled);

AssertionSeverity DefaultConcurrentAssertActionSeverity();

Region ConcurrentAssertActionRegion();

inline AssertActionBlockChoice SelectAssumeActionBlock(bool property_passed,
                                                       bool property_disabled) {
  return SelectAssertActionBlock(property_passed, property_disabled);
}

inline AssertActionBlockChoice ResolveAssumeActionUnderControl(
    AssertActionBlockChoice base, bool pass_action_enabled,
    bool fail_action_enabled) {
  return ResolveAssertActionUnderControl(base, pass_action_enabled,
                                         fail_action_enabled);
}

inline bool AssumeCallsDefaultErrorOnFailure(bool property_failed,
                                             bool has_else_clause,
                                             bool fail_action_enabled) {
  return property_failed && !has_else_clause && fail_action_enabled;
}

enum class BiasedAssertionDirective : uint8_t {
  kAssert,
  kAssume,
  kCover,
};

inline bool BiasingWeightsIgnored(BiasedAssertionDirective directive) {
  return directive == BiasedAssertionDirective::kAssert ||
         directive == BiasedAssertionDirective::kCover;
}

inline bool BiasedDistActsAsInside(BiasedAssertionDirective directive) {
  return BiasingWeightsIgnored(directive);
}

inline bool AssumeValueIsLegalUnderBiasing(int64_t value,
                                           const std::vector<int64_t>& members,
                                           bool) {
  for (int64_t member : members) {
    if (member == value) return true;
  }
  return false;
}

inline std::size_t SelectBiasedFreeVariable(
    const std::vector<uint32_t>& weights, uint64_t draw) {
  uint64_t cumulative = 0;
  for (std::size_t i = 0; i < weights.size(); ++i) {
    cumulative += weights[i];
    if (draw < cumulative) return i;
  }
  return weights.empty() ? 0 : weights.size() - 1;
}

bool RoseGclk(uint64_t prev_lsb, uint64_t cur_lsb);
bool FellGclk(uint64_t prev_lsb, uint64_t cur_lsb);
bool StableGclk(uint64_t prev_value, uint64_t cur_value);
bool ChangedGclk(uint64_t prev_value, uint64_t cur_value);

bool RisingGclk(uint64_t cur_lsb, uint64_t next_lsb);
bool FallingGclk(uint64_t cur_lsb, uint64_t next_lsb);
bool SteadyGclk(uint64_t cur_value, uint64_t next_value);
bool ChangingGclk(uint64_t cur_value, uint64_t next_value);

bool GclkFutureActionBlockDelayedToFollowingGlobalTick();

bool GclkFutureKillAffectsAttempt(bool kill_at_or_before_last_assertion_tick);

bool GclkFutureAttemptDisabledByDisableIff(uint64_t disable_active_time,
                                           uint64_t attempt_interval_end_time);

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

inline constexpr uint32_t kAssertionTypeDefault = 255;

inline constexpr uint32_t kDirectiveTypeDefault = 7;

enum class AssertionTypeBit : std::uint8_t {
  kConcurrent = 1,
  kSimpleImmediate = 2,
  kObservedDeferredImmediate = 4,
  kFinalDeferredImmediate = 8,
  kExpect = 16,
  kUnique = 32,
  kUnique0 = 64,
  kPriority = 128,
};

enum class DirectiveTypeBit : std::uint8_t {
  kAssert = 1,
  kCover = 2,
  kAssume = 4,
};

bool ControlAffectsAssertionType(uint32_t assertion_type_mask,
                                 AssertionTypeBit bit);

bool ControlAffectsDirectiveType(uint32_t directive_type_mask,
                                 DirectiveTypeBit bit);

bool ControlTypeAffectsStatistics(int control_type);

struct AssertControlInvocation {
  uint32_t control_type = 0;
  uint32_t assertion_type = 0;
  uint32_t directive_type = 0;
};

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

  void Lock(std::string_view inst);
  void Unlock(std::string_view inst);
  bool IsLocked(std::string_view inst) const;

  bool IsPassEnabled(std::string_view inst) const;
  void SetPassOff(std::string_view inst);
  void SetPassOn(std::string_view inst);

  bool IsVacuousPassEnabled(std::string_view inst) const;
  bool IsNonvacuousPassEnabled(std::string_view inst) const;
  void SetNonvacuousOn(std::string_view inst);
  void SetVacuousOff(std::string_view inst);

  bool IsFailEnabled(std::string_view inst) const;
  void SetFailOff(std::string_view inst);
  void SetFailOn(std::string_view inst);

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

enum class ExpectActionKind : uint8_t {
  kBlock,
  kRunPass,
  kRunFail,
  kReportError,
};

ExpectActionKind ResolveExpectAction(PropertyResult result,
                                     bool has_else_clause);

bool ExpectProcessRemainsBlocked(PropertyResult result);

bool ExpectClockingEventBeginsEvaluation(uint64_t activation_tick,
                                         uint64_t clocking_event_tick);

inline constexpr Region ExpectResumeRegion() { return Region::kReactive; }

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

  void ApplyDisableToProceduralAssertions(std::string_view process_id,
                                          DisableTarget target,
                                          std::string_view assertion_instance);

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

#endif
