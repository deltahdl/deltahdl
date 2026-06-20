#include "simulator/sva_engine.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/scheduler.h"

namespace delta {

void ProceduralAssertionQueue::Enqueue(PendingProceduralAssertion pending) {
  pending.matured = false;
  queue_.push_back(std::move(pending));
}

void ProceduralAssertionQueue::MatureAll() {
  for (auto& p : queue_) p.matured = true;
}

void ProceduralAssertionQueue::Flush() { queue_.clear(); }

void ProceduralAssertionQueue::FlushPending() {
  std::erase_if(queue_,
                [](const PendingProceduralAssertion& p) { return !p.matured; });
}

void ProceduralAssertionQueue::FlushPendingForInstance(
    std::string_view instance_name) {
  std::erase_if(queue_, [&](const PendingProceduralAssertion& p) {
    return !p.matured && p.instance_name == instance_name;
  });
}

uint32_t ProceduralAssertionQueue::Size() const {
  return static_cast<uint32_t>(queue_.size());
}

uint32_t ProceduralAssertionQueue::MaturedCount() const {
  uint32_t n = 0;
  for (const auto& p : queue_) {
    if (p.matured) ++n;
  }
  return n;
}

bool IsProceduralAssertionFlushPoint(FlushPointReason reason) {
  switch (reason) {
    case FlushPointReason::kEventControlResume:
    case FlushPointReason::kWaitResume:
    case FlushPointReason::kAlwaysCombSignalDelta:
    case FlushPointReason::kAlwaysLatchSignalDelta:
    case FlushPointReason::kDisableOuterScope:
      return true;
    case FlushPointReason::kNone:
      return false;
  }
  return false;
}

bool DisableFlushesProceduralAssertions(DisableTarget target) {
  switch (target) {
    case DisableTarget::kSpecificAssertion:
    case DisableTarget::kOutermostScope:
      return true;
    case DisableTarget::kNonOutermostScope:
    case DisableTarget::kTask:
      return false;
  }
  return false;
}

bool DisableFlushesDeferredAssertions(DisableTarget target) {
  switch (target) {
    case DisableTarget::kSpecificAssertion:
    case DisableTarget::kOutermostScope:
      return true;
    case DisableTarget::kNonOutermostScope:
    case DisableTarget::kTask:
      return false;
  }
  return false;
}

bool IsStaticConcurrentAssertion(bool appears_in_procedural_code) {
  return !appears_in_procedural_code;
}

bool IsAutomaticAllowedInClockingEvent(bool variable_is_automatic) {
  return !variable_is_automatic;
}

InferredClock InferClockForProceduralConcurrentAssertion(
    std::string_view proc_context_clock, std::string_view default_clock) {
  if (!proc_context_clock.empty()) {
    return InferredClock{InferredClockKind::kFromProceduralContext,
                         proc_context_clock};
  }
  if (!default_clock.empty()) {
    return InferredClock{InferredClockKind::kFromDefaultClocking,
                         default_clock};
  }
  return InferredClock{InferredClockKind::kNotInferrable, {}};
}

bool SatisfiesClockInferenceRequirements(bool no_blocking_timing_control,
                                         bool exactly_one_event_control,
                                         bool unique_qualifying_event_expr) {
  return no_blocking_timing_control && exactly_one_event_control &&
         unique_qualifying_event_expr;
}

void MaturedAssertionQueue::Place(PendingProceduralAssertion matured) {
  matured.matured = true;
  queue_.push_back(std::move(matured));
}

std::vector<PendingProceduralAssertion> MaturedAssertionQueue::TakeAll() {
  return std::exchange(queue_, {});
}

uint32_t MaturedAssertionQueue::Size() const {
  return static_cast<uint32_t>(queue_.size());
}

void ExecuteDeferredAssertionAction(const DeferredAssertion& da) {
  if (da.condition_val != 0) {
    if (da.pass_action) da.pass_action();
  } else {
    if (da.fail_action) da.fail_action();
  }
}

bool UsesErrorSeverityFallback(const DeferredAssertion& da) {
  if (da.condition_val != 0) return false;
  if (da.kind == AssertionKind::kCover) return false;
  return !da.has_else_clause;
}

AssertActionBlockChoice SelectAssertActionBlock(bool property_passed,
                                                bool property_disabled) {
  if (property_disabled) return AssertActionBlockChoice::kNone;
  return property_passed ? AssertActionBlockChoice::kPass
                         : AssertActionBlockChoice::kFail;
}

AssertActionBlockChoice ResolveAssertActionUnderControl(
    AssertActionBlockChoice base, bool pass_action_enabled,
    bool fail_action_enabled) {
  if (base == AssertActionBlockChoice::kPass && !pass_action_enabled) {
    return AssertActionBlockChoice::kNone;
  }
  if (base == AssertActionBlockChoice::kFail && !fail_action_enabled) {
    return AssertActionBlockChoice::kNone;
  }
  return base;
}

bool CallsDefaultErrorOnFailure(const DeferredAssertion& da,
                                bool fail_action_enabled) {
  return UsesErrorSeverityFallback(da) && fail_action_enabled;
}

AssertionSeverity DefaultConcurrentAssertActionSeverity() {
  return AssertionSeverity::kError;
}

Region ConcurrentAssertActionRegion() { return Region::kReactive; }

// §16.14.4: the same semantics as assume property — a restrict directs the tool
// to take its property as a constraint and prunes the state space identically.
bool RestrictSharesAssumeConstraintSemantics() { return true; }

// §16.14.4: a restrict property is not verified in simulation.
bool RestrictIsVerifiedInSimulation() { return false; }

// §16.14.4: a simulation cycle that violates the restriction is not an error,
// since the statement is never checked there.
bool RestrictViolationIsSimulationError() { return false; }

// §16.14.5: under `always` semantics a fresh evaluation attempt begins at every
// occurrence of the leading clock event, so over the run the number of attempts
// started equals the number of leading clock ticks.
int StaticConcurrentAssertionAttemptsStarted(int leading_clock_ticks) {
  return leading_clock_ticks;
}

// §16.14.5: the bare assert form and the explicit `always` assert form are
// equivalent.
bool StaticAssertEquivalentToAlwaysAssert() { return true; }

// §16.14.5: the bare cover form and the explicit `always` cover form are
// equivalent.
bool StaticCoverEquivalentToAlwaysCover() { return true; }

bool RoseGclk(uint64_t prev_lsb, uint64_t cur_lsb) {
  return (prev_lsb & 1u) == 0u && (cur_lsb & 1u) == 1u;
}

bool FellGclk(uint64_t prev_lsb, uint64_t cur_lsb) {
  return (prev_lsb & 1u) == 1u && (cur_lsb & 1u) == 0u;
}

bool StableGclk(uint64_t prev_value, uint64_t cur_value) {
  return prev_value == cur_value;
}

bool ChangedGclk(uint64_t prev_value, uint64_t cur_value) {
  return prev_value != cur_value;
}

bool RisingGclk(uint64_t cur_lsb, uint64_t next_lsb) {
  return (cur_lsb & 1u) == 0u && (next_lsb & 1u) == 1u;
}

bool FallingGclk(uint64_t cur_lsb, uint64_t next_lsb) {
  return (cur_lsb & 1u) == 1u && (next_lsb & 1u) == 0u;
}

bool SteadyGclk(uint64_t cur_value, uint64_t next_value) {
  return cur_value == next_value;
}

bool ChangingGclk(uint64_t cur_value, uint64_t next_value) {
  return !SteadyGclk(cur_value, next_value);
}

bool GclkFutureActionBlockDelayedToFollowingGlobalTick() { return true; }

bool GclkFutureKillAffectsAttempt(bool kill_at_or_before_last_assertion_tick) {
  return kill_at_or_before_last_assertion_tick;
}

bool ControlTypeAffectsStatistics(int control_type) {
  return control_type >= static_cast<int>(AssertControlType::kLock) &&
         control_type <= static_cast<int>(AssertControlType::kKill);
}

bool ControlAffectsAssertionType(uint32_t assertion_type_mask,
                                 AssertionTypeBit bit) {
  return (assertion_type_mask & static_cast<uint32_t>(bit)) != 0;
}

bool ControlAffectsDirectiveType(uint32_t directive_type_mask,
                                 DirectiveTypeBit bit) {
  return (directive_type_mask & static_cast<uint32_t>(bit)) != 0;
}

bool EquivalentAssertControlForTask(std::string_view task_name,
                                    AssertControlInvocation& out) {
  // §20.11: $asserton/$assertoff/$assertkill use assertion_type 15; the action
  // control tasks use assertion_type 31. Both families use directive_type 7.
  constexpr uint32_t kStatusAssertionType = 15;
  constexpr uint32_t kActionAssertionType = 31;
  constexpr uint32_t kDirective = 7;
  auto set = [&](uint32_t control_type, uint32_t assertion_type) {
    out.control_type = control_type;
    out.assertion_type = assertion_type;
    out.directive_type = kDirective;
    return true;
  };
  if (task_name == "$asserton") {
    return set(static_cast<uint32_t>(AssertControlType::kOn),
               kStatusAssertionType);
  }
  if (task_name == "$assertoff") {
    return set(static_cast<uint32_t>(AssertControlType::kOff),
               kStatusAssertionType);
  }
  if (task_name == "$assertkill") {
    return set(static_cast<uint32_t>(AssertControlType::kKill),
               kStatusAssertionType);
  }
  if (task_name == "$assertpasson") {
    return set(static_cast<uint32_t>(AssertControlType::kPassOn),
               kActionAssertionType);
  }
  if (task_name == "$assertpassoff") {
    return set(static_cast<uint32_t>(AssertControlType::kPassOff),
               kActionAssertionType);
  }
  if (task_name == "$assertfailon") {
    return set(static_cast<uint32_t>(AssertControlType::kFailOn),
               kActionAssertionType);
  }
  if (task_name == "$assertfailoff") {
    return set(static_cast<uint32_t>(AssertControlType::kFailOff),
               kActionAssertionType);
  }
  if (task_name == "$assertnonvacuouson") {
    return set(static_cast<uint32_t>(AssertControlType::kNonvacuousOn),
               kActionAssertionType);
  }
  if (task_name == "$assertvacuousoff") {
    return set(static_cast<uint32_t>(AssertControlType::kVacuousOff),
               kActionAssertionType);
  }
  return false;
}

bool IsDeferredFlushPoint(FlushPointReason reason) {
  switch (reason) {
    case FlushPointReason::kEventControlResume:
    case FlushPointReason::kWaitResume:
    case FlushPointReason::kAlwaysCombSignalDelta:
    case FlushPointReason::kAlwaysLatchSignalDelta:
    case FlushPointReason::kDisableOuterScope:
      return true;
    case FlushPointReason::kNone:
      return false;
  }
  return false;
}

void DeferredReportQueue::Enqueue(PendingDeferredReport report) {
  report.matured = false;
  entries_.push_back(std::move(report));
}

void DeferredReportQueue::MatureObservedReports() {
  for (auto& e : entries_) {
    if (e.deferral == DeferralKind::kObserved) e.matured = true;
  }
}

void DeferredReportQueue::MatureFinalReports() {
  for (auto& e : entries_) {
    if (e.deferral == DeferralKind::kFinal) e.matured = true;
  }
}

std::vector<PendingDeferredReport> DeferredReportQueue::TakeMaturedObserved() {
  std::vector<PendingDeferredReport> taken;
  std::vector<PendingDeferredReport> kept;
  kept.reserve(entries_.size());
  for (auto& e : entries_) {
    if (e.matured && e.deferral == DeferralKind::kObserved) {
      taken.push_back(std::move(e));
    } else {
      kept.push_back(std::move(e));
    }
  }
  entries_ = std::move(kept);
  return taken;
}

std::vector<PendingDeferredReport> DeferredReportQueue::TakeMaturedFinal() {
  std::vector<PendingDeferredReport> taken;
  std::vector<PendingDeferredReport> kept;
  kept.reserve(entries_.size());
  for (auto& e : entries_) {
    if (e.matured && e.deferral == DeferralKind::kFinal) {
      taken.push_back(std::move(e));
    } else {
      kept.push_back(std::move(e));
    }
  }
  entries_ = std::move(kept);
  return taken;
}

void DeferredReportQueue::FlushNonMatured() {
  std::vector<PendingDeferredReport> kept;
  kept.reserve(entries_.size());
  for (auto& e : entries_) {
    if (e.matured) kept.push_back(std::move(e));
  }
  entries_ = std::move(kept);
}

void DeferredReportQueue::FlushNonMaturedForInstance(
    std::string_view instance_name) {
  std::erase_if(entries_, [&](const PendingDeferredReport& e) {
    return !e.matured && e.da.instance_name == instance_name;
  });
}

uint32_t DeferredReportQueue::Size() const {
  return static_cast<uint32_t>(entries_.size());
}

uint32_t DeferredReportQueue::MaturedCount() const {
  uint32_t n = 0;
  for (const auto& e : entries_) {
    if (e.matured) ++n;
  }
  return n;
}

uint32_t DeferredReportQueue::NonMaturedCount() const {
  return Size() - MaturedCount();
}

bool AssertionControl::IsEnabled(std::string_view inst) const {
  if (global_off_) return false;
  return disabled_.find(std::string(inst)) == disabled_.end() &&
         killed_.find(std::string(inst)) == killed_.end();
}

void AssertionControl::SetOff(std::string_view inst) {
  if (IsLocked(inst)) return;
  disabled_.insert(std::string(inst));
}

void AssertionControl::SetOn(std::string_view inst) {
  if (IsLocked(inst)) return;
  disabled_.erase(std::string(inst));
}

void AssertionControl::Kill(std::string_view inst) {
  if (IsLocked(inst)) return;
  killed_.insert(std::string(inst));
  disabled_.insert(std::string(inst));
}

bool AssertionControl::WasKilled(std::string_view inst) const {
  return killed_.find(std::string(inst)) != killed_.end();
}

void AssertionControl::SetGlobalOff() { global_off_ = true; }

void AssertionControl::SetGlobalOn() { global_off_ = false; }

void AssertionControl::Lock(std::string_view inst) {
  locked_.insert(std::string(inst));
}

void AssertionControl::Unlock(std::string_view inst) {
  locked_.erase(std::string(inst));
}

bool AssertionControl::IsLocked(std::string_view inst) const {
  return locked_.find(std::string(inst)) != locked_.end();
}

bool AssertionControl::IsPassEnabled(std::string_view inst) const {
  return IsVacuousPassEnabled(inst) && IsNonvacuousPassEnabled(inst);
}

void AssertionControl::SetPassOff(std::string_view inst) {
  if (IsLocked(inst)) return;
  vacuous_pass_off_.insert(std::string(inst));
  nonvacuous_pass_off_.insert(std::string(inst));
}

void AssertionControl::SetPassOn(std::string_view inst) {
  if (IsLocked(inst)) return;
  vacuous_pass_off_.erase(std::string(inst));
  nonvacuous_pass_off_.erase(std::string(inst));
}

bool AssertionControl::IsVacuousPassEnabled(std::string_view inst) const {
  return vacuous_pass_off_.find(std::string(inst)) == vacuous_pass_off_.end();
}

bool AssertionControl::IsNonvacuousPassEnabled(std::string_view inst) const {
  return nonvacuous_pass_off_.find(std::string(inst)) ==
         nonvacuous_pass_off_.end();
}

void AssertionControl::SetNonvacuousOn(std::string_view inst) {
  if (IsLocked(inst)) return;
  nonvacuous_pass_off_.erase(std::string(inst));
}

void AssertionControl::SetVacuousOff(std::string_view inst) {
  if (IsLocked(inst)) return;
  vacuous_pass_off_.insert(std::string(inst));
}

bool AssertionControl::IsFailEnabled(std::string_view inst) const {
  return fail_off_.find(std::string(inst)) == fail_off_.end();
}

void AssertionControl::SetFailOff(std::string_view inst) {
  if (IsLocked(inst)) return;
  fail_off_.insert(std::string(inst));
}

void AssertionControl::SetFailOn(std::string_view inst) {
  if (IsLocked(inst)) return;
  fail_off_.erase(std::string(inst));
}

void AssertionControl::ApplyControl(int control_type, std::string_view inst) {
  // §20.11: Unlock is the only control that reaches a locked assertion; every
  // other control_type is a no-op while the assertion is locked.
  if (control_type == static_cast<int>(AssertControlType::kUnlock)) {
    Unlock(inst);
    return;
  }
  if (IsLocked(inst)) return;
  switch (static_cast<AssertControlType>(control_type)) {
    case AssertControlType::kLock:
      Lock(inst);
      break;
    case AssertControlType::kUnlock:
      Unlock(inst);
      break;
    case AssertControlType::kOn:
      SetOn(inst);
      break;
    case AssertControlType::kOff:
      SetOff(inst);
      break;
    case AssertControlType::kKill:
      Kill(inst);
      break;
    case AssertControlType::kPassOn:
      SetPassOn(inst);
      break;
    case AssertControlType::kPassOff:
      SetPassOff(inst);
      break;
    case AssertControlType::kFailOn:
      SetFailOn(inst);
      break;
    case AssertControlType::kFailOff:
      SetFailOff(inst);
      break;
    case AssertControlType::kNonvacuousOn:
      SetNonvacuousOn(inst);
      break;
    case AssertControlType::kVacuousOff:
      SetVacuousOff(inst);
      break;
  }
}

void SvaEngine::QueueDeferredAssertion(const DeferredAssertion& da) {
  deferred_queue_.push_back(da);
}

void SvaEngine::QueueDeferredAssertionIfEnabled(const DeferredAssertion& da) {
  if (!control_.IsEnabled(da.instance_name)) return;
  deferred_queue_.push_back(da);
}

void SvaEngine::FlushDeferredAssertions(Scheduler& sched, SimTime time) {
  auto queue = std::move(deferred_queue_);
  deferred_queue_.clear();
  for (auto& da : queue) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [da_copy = std::move(da)]() {
      ExecuteDeferredAssertionAction(da_copy);
    };
    sched.ScheduleEvent(time, Region::kObserved, event);
  }
}

void SvaEngine::FlushDeferredAssertionsRespectingControl(Scheduler& sched,
                                                         SimTime time) {
  auto queue = std::move(deferred_queue_);
  deferred_queue_.clear();
  for (auto& da : queue) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [this, da_copy = std::move(da)]() {
      bool is_pass = (da_copy.condition_val != 0);
      if (is_pass && !control_.IsPassEnabled(da_copy.instance_name)) return;
      if (!is_pass && !control_.IsFailEnabled(da_copy.instance_name)) return;
      ExecuteDeferredAssertionAction(da_copy);
    };
    sched.ScheduleEvent(time, Region::kObserved, event);
  }
}

void SvaEngine::KillAssertionsForInstance(std::string_view inst) {
  control_.Kill(inst);
  std::string inst_str(inst);
  std::erase_if(deferred_queue_, [&inst_str](const DeferredAssertion& da) {
    return da.instance_name == inst_str;
  });
}

uint32_t SvaEngine::DeferredQueueSize() const {
  return static_cast<uint32_t>(deferred_queue_.size());
}

ProceduralAssertionQueue& SvaEngine::GetProceduralQueue(
    std::string_view process_id) {
  return procedural_queues_[std::string(process_id)];
}

DeferredReportQueue& SvaEngine::GetDeferredReportQueue(
    std::string_view process_id) {
  return per_process_reports_[std::string(process_id)];
}

const DeferredReportQueue* SvaEngine::PeekDeferredReportQueue(
    std::string_view process_id) const {
  auto it = per_process_reports_.find(std::string(process_id));
  if (it == per_process_reports_.end()) return nullptr;
  return &it->second;
}

void SvaEngine::QueuePendingReport(std::string_view process_id,
                                   const DeferredAssertion& da,
                                   DeferralKind kind) {
  PendingDeferredReport report;
  report.process_id = std::string(process_id);
  report.deferral = kind;
  report.da = da;
  GetDeferredReportQueue(process_id).Enqueue(std::move(report));
}

void SvaEngine::MatureObservedReports(std::string_view process_id) {
  GetDeferredReportQueue(process_id).MatureObservedReports();
}

void SvaEngine::MatureFinalReports(std::string_view process_id) {
  GetDeferredReportQueue(process_id).MatureFinalReports();
}

uint32_t SvaEngine::ExecuteMaturedObservedInReactive(
    std::string_view process_id, Scheduler& sched, SimTime time) {
  auto matured = GetDeferredReportQueue(process_id).TakeMaturedObserved();
  for (auto& report : matured) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [da_copy = std::move(report.da)]() {
      ExecuteDeferredAssertionAction(da_copy);
    };
    sched.ScheduleEvent(time, Region::kReactive, event);
  }
  return static_cast<uint32_t>(matured.size());
}

uint32_t SvaEngine::ExecuteMaturedFinalInPostponed(std::string_view process_id,
                                                   Scheduler& sched,
                                                   SimTime time) {
  auto matured = GetDeferredReportQueue(process_id).TakeMaturedFinal();
  for (auto& report : matured) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [da_copy = std::move(report.da)]() {
      ExecuteDeferredAssertionAction(da_copy);
    };
    sched.ScheduleEvent(time, Region::kPostponed, event);
  }
  return static_cast<uint32_t>(matured.size());
}

void SvaEngine::OnDeferredFlushPoint(std::string_view process_id,
                                     FlushPointReason reason) {
  if (!IsDeferredFlushPoint(reason)) return;
  GetDeferredReportQueue(process_id).FlushNonMatured();
}

void SvaEngine::OnProceduralAssertionFlushPoint(std::string_view process_id,
                                                FlushPointReason reason) {
  if (!IsProceduralAssertionFlushPoint(reason)) return;
  GetProceduralQueue(process_id).FlushPending();
}

void SvaEngine::ApplyDisableToProceduralAssertions(
    std::string_view process_id, DisableTarget target,
    std::string_view assertion_instance) {
  if (!DisableFlushesProceduralAssertions(target)) return;
  if (target == DisableTarget::kSpecificAssertion) {
    GetProceduralQueue(process_id).FlushPendingForInstance(assertion_instance);
  } else {
    GetProceduralQueue(process_id).FlushPending();
  }
}

void SvaEngine::ApplyDisableToDeferredAssertions(
    std::string_view process_id, DisableTarget target,
    std::string_view assertion_instance) {
  if (!DisableFlushesDeferredAssertions(target)) return;
  if (target == DisableTarget::kSpecificAssertion) {
    GetDeferredReportQueue(process_id)
        .FlushNonMaturedForInstance(assertion_instance);
  } else {
    GetDeferredReportQueue(process_id).FlushNonMatured();
  }
}

ExpectActionKind ResolveExpectAction(PropertyResult result,
                                     bool has_else_clause) {
  // §16.17: a pending property keeps the process blocked; a resolved property
  // selects which arm of the action block runs.
  switch (result) {
    case PropertyResult::kPending:
      return ExpectActionKind::kBlock;
    case PropertyResult::kPass:
    case PropertyResult::kVacuousPass:
      return ExpectActionKind::kRunPass;
    case PropertyResult::kFail:
      return has_else_clause ? ExpectActionKind::kRunFail
                             : ExpectActionKind::kReportError;
  }
  return ExpectActionKind::kBlock;
}

bool ExpectProcessRemainsBlocked(PropertyResult result) {
  // §16.17: the process unblocks only once the property succeeds or fails.
  return result == PropertyResult::kPending;
}

bool ExpectClockingEventBeginsEvaluation(uint64_t activation_tick,
                                         uint64_t clocking_event_tick) {
  // §16.17: the first evaluation is on the next clocking event after the expect
  // executes, not on one coincident with activation.
  return clocking_event_tick > activation_tick;
}

}  // namespace delta
