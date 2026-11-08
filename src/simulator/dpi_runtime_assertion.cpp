#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/sva_engine_sequences.h"

namespace delta {

namespace {
AssertionApi* g_assertion_api = nullptr;
}  // namespace

AssertionApi& GetGlobalAssertionApi() {
  static AssertionApi default_api;
  if (g_assertion_api != nullptr) return *g_assertion_api;
  return default_api;
}

void SetGlobalAssertionApi(AssertionApi* api) { g_assertion_api = api; }

void AssertionApi::RegisterCallback(int reason, AssertionCbFunc cb,
                                    void* user_data) {
  callbacks_.push_back({reason, std::move(cb), user_data});
}

void AssertionApi::FireCallback(const AssertionCbData& data) {
  for (auto& entry : callbacks_) {
    if (entry.reason == data.reason) {
      entry.cb(data);
    }
  }
}

uint32_t AssertionApi::CallbackCount() const {
  return static_cast<uint32_t>(callbacks_.size());
}

namespace {

bool IsStepReason(int reason) {
  return reason == cbAssertionStepSuccess || reason == cbAssertionStepFailure;
}

}  // namespace

std::string AssertionKey(std::string_view scope, std::string_view name,
                         uint32_t line, uint32_t column) {
  std::string key(scope);
  if (!key.empty()) key += '.';
  if (!name.empty()) return key.append(name);
  return key + "@" + std::to_string(line) + ":" + std::to_string(column);
}

bool AssertionApi::IsAssertionCallbackReason(int reason) {
  switch (reason) {
    case cbAssertionStart:
    case cbAssertionSuccess:
    case cbAssertionVacuousSuccess:
    case cbAssertionDisabledEvaluation:
    case cbAssertionFailure:
    case cbAssertionStepSuccess:
    case cbAssertionStepFailure:
    case cbAssertionLock:
    case cbAssertionUnlock:
    case cbAssertionDisable:
    case cbAssertionEnable:
    case cbAssertionReset:
    case cbAssertionKill:
    case cbAssertionDisablePassAction:
    case cbAssertionEnablePassAction:
    case cbAssertionDisableFailAction:
    case cbAssertionEnableFailAction:
    case cbAssertionDisableVacuousAction:
    case cbAssertionEnableNonvacuousAction:
      return true;
    default:
      return false;
  }
}

bool AssertionApi::IsAssertionSysCallbackReason(int reason) {
  switch (reason) {
    case cbAssertionSysInitialized:
    case cbAssertionSysLock:
    case cbAssertionSysUnlock:
    case cbAssertionSysOn:
    case cbAssertionSysOff:
    case cbAssertionSysKill:
    case cbAssertionSysEnd:
    case cbAssertionSysReset:
    case cbAssertionSysEnablePassAction:
    case cbAssertionSysEnableFailAction:
    case cbAssertionSysDisablePassAction:
    case cbAssertionSysDisableFailAction:
    case cbAssertionSysEnableNonvacuousAction:
    case cbAssertionSysDisableVacuousAction:
      return true;
    default:
      return false;
  }
}

bool AssertionApi::IsReasonValidForHandle(int reason, int handle_type) {
  if (!IsAssertionCallbackReason(reason)) return false;
  if (IsAssertionStatementHandle(handle_type)) return true;
  if (handle_type == vpiSequenceInst || handle_type == vpiPropertyInst) {
    return reason == cbAssertionStart || reason == cbAssertionSuccess ||
           reason == cbAssertionFailure;
  }
  return false;
}

bool AssertionApi::ReasonCarriesAttemptInfo(int reason) {
  switch (reason) {
    case cbAssertionLock:
    case cbAssertionUnlock:
    case cbAssertionDisable:
    case cbAssertionEnable:
    case cbAssertionReset:
    case cbAssertionKill:
    case cbAssertionDisablePassAction:
    case cbAssertionEnablePassAction:
    case cbAssertionDisableFailAction:
    case cbAssertionEnableFailAction:
    case cbAssertionDisableVacuousAction:
    case cbAssertionEnableNonvacuousAction:
      return false;
    default:
      return true;
  }
}

bool AssertionApi::IsValidFailingStep(const AssertionStepDetail& step) {
  return !step.matched_exprs.empty();
}

AssertionCallbackHandle AssertionApi::PlaceAssertionCallback(
    int reason, std::string_view assertion, int handle_type,
    AssertionPlacedCallback cb, void* user_data) {
  if (assertion.empty()) return 0;
  if (!IsReasonValidForHandle(reason, handle_type)) return 0;

  AssertionCallbackHandle handle = next_callback_handle_++;
  placed_callbacks_.push_back(
      {handle, reason, std::string(assertion), std::move(cb), user_data});
  return handle;
}

bool AssertionApi::RemoveAssertionCallback(AssertionCallbackHandle handle) {
  if (handle == 0) return false;
  auto before = placed_callbacks_.size();
  std::erase_if(placed_callbacks_,
                [handle](const PlacedCb& e) { return e.handle == handle; });
  return placed_callbacks_.size() != before;
}

void AssertionApi::NoteControlTarget(std::string_view assertion,
                                     AssertionControlTarget target) {
  control_targets_.insert_or_assign(std::string(assertion), std::move(target));
}

uint32_t AssertionApi::PlacedCallbackCount() const {
  return static_cast<uint32_t>(placed_callbacks_.size());
}

uint32_t AssertionApi::DeliverAssertionEvent(std::string_view assertion,
                                             int reason, uint64_t cb_time,
                                             const AssertionAttemptInfo& info) {
  if (reason == cbAssertionStepFailure && !IsValidFailingStep(info.step)) {
    return 0;
  }

  AssertionCallbackArgs args;
  args.reason = reason;
  args.cb_time = cb_time;
  args.assertion = std::string(assertion);
  args.user_data = nullptr;
  const AssertionAttemptInfo* info_ptr =
      ReasonCarriesAttemptInfo(reason) ? &info : nullptr;
  args.info = info_ptr;

  uint32_t fired = 0;
  for (auto& entry : placed_callbacks_) {
    if (std::string_view(entry.assertion) != assertion) continue;
    bool matches = IsStepReason(entry.reason) ? IsStepReason(reason)
                                              : entry.reason == reason;
    if (!matches) continue;
    args.user_data = entry.user_data;
    entry.cb(args);
    ++fired;
  }
  return fired;
}

void AssertionApi::SetGlobalClockTicks(std::vector<uint64_t> ticks) {
  global_clock_ticks_ = std::move(ticks);
}

void AssertionApi::MarkAssertionUsesGlobalClockingFuture(
    std::string_view assertion) {
  global_clocking_future_assertions_.emplace(assertion);
}

bool AssertionApi::AssertionUsesGlobalClockingFuture(
    std::string_view assertion) const {
  return global_clocking_future_assertions_.count(std::string(assertion)) != 0;
}

uint64_t AssertionApi::NearestGlobalClockTickAfter(
    const std::vector<uint64_t>& ticks, uint64_t event_time) {
  uint64_t nearest = kNoGlobalClockTick;
  for (uint64_t tick : ticks) {
    if (tick > event_time && tick < nearest) nearest = tick;
  }
  return nearest;
}

uint32_t AssertionApi::DeliverAssertionEventAtGlobalClock(
    std::string_view assertion, int reason, uint64_t event_time,
    const AssertionAttemptInfo& info) {
  if (!AssertionUsesGlobalClockingFuture(assertion)) {
    return DeliverAssertionEvent(assertion, reason, event_time, info);
  }
  uint64_t delivery_time =
      NearestGlobalClockTickAfter(global_clock_ticks_, event_time);
  pending_global_clocking_cbs_.push_back(
      {std::string(assertion), reason, event_time, delivery_time, info});
  return 0;
}

uint32_t AssertionApi::AdvanceGlobalClockTick(uint64_t tick_time) {
  uint32_t fired = 0;
  std::vector<PendingGlobalClockingCb> still_waiting;
  for (auto& pending : pending_global_clocking_cbs_) {
    if (pending.delivery_time <= tick_time) {
      fired += DeliverAssertionEvent(pending.assertion, pending.reason,
                                     pending.event_time, pending.info);
    } else {
      still_waiting.push_back(std::move(pending));
    }
  }
  pending_global_clocking_cbs_ = std::move(still_waiting);
  return fired;
}

uint32_t AssertionApi::PendingGlobalClockingCallbackCount() const {
  return static_cast<uint32_t>(pending_global_clocking_cbs_.size());
}

void AssertionApi::SetSeverity(std::string_view name, AssertionSeverity sev) {
  severity_map_[std::string(name)] = sev;
}

AssertionSeverity AssertionApi::GetSeverity(std::string_view name) const {
  auto it = severity_map_.find(std::string(name));
  if (it == severity_map_.end()) return AssertionSeverity::kError;
  return it->second;
}

void AssertionApi::SetAction(std::string_view name, AssertionAction action) {
  action_map_[std::string(name)] = action;
}

AssertionAction AssertionApi::GetAction(std::string_view name) const {
  auto it = action_map_.find(std::string(name));
  if (it == action_map_.end()) return AssertionAction::kNone;
  return it->second;
}

namespace {

struct SysControlState {
  uint32_t& attempts_in_progress;
  bool& started;
  bool& ended;
  bool& fail_action_enabled;
  bool& vacuous_action_enabled;
  bool& nonvacuous_action_enabled;
};

bool IsStepCallbackReason(int reason) {
  return reason == cbAssertionStepSuccess || reason == cbAssertionStepFailure;
}

template <typename CallbackVec, typename PlacedVec>
void ApplySysReset(const SysControlState& s, CallbackVec& callbacks,
                   PlacedVec& placed) {
  s.attempts_in_progress = 0;
  s.started = true;
  s.fail_action_enabled = true;
  s.vacuous_action_enabled = true;
  s.nonvacuous_action_enabled = true;
  auto is_step = [](const auto& e) { return IsStepCallbackReason(e.reason); };
  std::erase_if(callbacks, is_step);
  std::erase_if(placed, is_step);
}

void ApplySysKill(const SysControlState& s) {
  s.attempts_in_progress = 0;
  s.started = false;
}

template <typename CallbackVec, typename PlacedVec>
void ApplySysEnd(const SysControlState& s, CallbackVec& callbacks,
                 PlacedVec& placed) {
  s.attempts_in_progress = 0;
  s.started = false;
  s.ended = true;
  callbacks.clear();
  placed.clear();
}

}  // namespace

bool AssertionApi::SysControl(int control, std::string_view scope) {
  if (ended_) return false;
  if (locked_ && control != vpiAssertionSysUnlock) return false;

  last_control_global_ = scope.empty();

  const SysControlState kState{attempts_in_progress_,
                               started_,
                               ended_,
                               fail_action_enabled_,
                               vacuous_action_enabled_,
                               nonvacuous_action_enabled_};

  switch (control) {
    case vpiAssertionSysReset:
      ApplySysReset(kState, callbacks_, placed_callbacks_);
      FlushAllPendingAssertionReports();
      return true;
    case vpiAssertionSysOff:
      started_ = false;
      return true;
    case vpiAssertionSysKill:
      ApplySysKill(kState);
      FlushAllPendingAssertionReports();
      return true;
    case vpiAssertionSysLock:
      locked_ = true;
      return true;
    case vpiAssertionSysUnlock:
      locked_ = false;
      return true;
    case vpiAssertionSysOn:
      started_ = true;
      return true;
    case vpiAssertionSysEnd:
      ApplySysEnd(kState, callbacks_, placed_callbacks_);
      FlushAllPendingAssertionReports();
      return true;
    case vpiAssertionSysDisablePassAction:
      vacuous_action_enabled_ = false;
      nonvacuous_action_enabled_ = false;
      return true;
    case vpiAssertionSysEnablePassAction:
      vacuous_action_enabled_ = true;
      nonvacuous_action_enabled_ = true;
      return true;
    case vpiAssertionSysDisableFailAction:
      fail_action_enabled_ = false;
      return true;
    case vpiAssertionSysEnableFailAction:
      fail_action_enabled_ = true;
      return true;
    case vpiAssertionSysDisableVacuousAction:
      vacuous_action_enabled_ = false;
      return true;
    case vpiAssertionSysEnableNonvacuousAction:
      nonvacuous_action_enabled_ = true;
      return true;
    default:
      return false;
  }
}

bool AssertionApi::IsAssertionStatementHandle(int vpi_type) {
  switch (vpi_type) {
    case vpiAssert:
    case vpiAssume:
    case vpiCover:
    case vpiRestrict:
    case vpiImmediateAssert:
    case vpiImmediateAssume:
    case vpiImmediateCover:
      return true;
    default:
      return false;
  }
}

AssertionApi::AssertionControlState& AssertionApi::StateFor(
    std::string_view assertion) {
  return assertion_state_[std::string(assertion)];
}

const AssertionApi::AssertionControlState* AssertionApi::FindState(
    std::string_view assertion) const {
  auto it = assertion_state_.find(std::string(assertion));
  return it == assertion_state_.end() ? nullptr : &it->second;
}

void AssertionApi::QueuePendingAssertionReport(std::string_view assertion) {
  ++pending_assertion_reports_[std::string(assertion)];
}

uint32_t AssertionApi::PendingAssertionReportCount(
    std::string_view assertion) const {
  auto it = pending_assertion_reports_.find(std::string(assertion));
  return it == pending_assertion_reports_.end() ? 0u : it->second;
}

void AssertionApi::FlushPendingAssertionReports(std::string_view assertion) {
  pending_assertion_reports_.erase(std::string(assertion));
}

void AssertionApi::FlushAllPendingAssertionReports() {
  pending_assertion_reports_.clear();
}

bool AssertionApi::Control(int control, std::string_view assertion) {
  if (assertion.empty() || SystemRefusesControl()) return false;
  AssertionControlState& s = StateFor(assertion);
  if (s.locked && control != vpiAssertionUnlock) return false;

  switch (control) {
    case vpiAssertionReset:
      s.attempts.clear();
      s.enabled = true;
      s.fail_action_enabled = true;
      s.vacuous_action_enabled = true;
      s.nonvacuous_action_enabled = true;
      FlushPendingAssertionReports(assertion);
      return true;
    case vpiAssertionLock:
      s.locked = true;
      return true;
    case vpiAssertionUnlock:
      s.locked = false;
      return true;
    case vpiAssertionDisable:
      s.enabled = false;
      return true;
    case vpiAssertionEnable:
      s.enabled = true;
      return true;
    case vpiAssertionDisablePassAction:
      s.vacuous_action_enabled = false;
      s.nonvacuous_action_enabled = false;
      return true;
    case vpiAssertionEnablePassAction:
      s.vacuous_action_enabled = true;
      s.nonvacuous_action_enabled = true;
      return true;
    case vpiAssertionDisableFailAction:
      s.fail_action_enabled = false;
      return true;
    case vpiAssertionEnableFailAction:
      s.fail_action_enabled = true;
      return true;
    case vpiAssertionDisableVacuousAction:
      s.vacuous_action_enabled = false;
      return true;
    case vpiAssertionEnableNonvacuousAction:
      s.nonvacuous_action_enabled = true;
      return true;
    default:
      return false;
  }
}

bool AssertionApi::ControlAttempt(int control, std::string_view assertion,
                                  uint64_t attempt_start_time) {
  if (assertion.empty() || SystemRefusesControl()) return false;
  AssertionControlState& s = StateFor(assertion);
  if (s.locked && control != vpiAssertionUnlock) return false;

  switch (control) {
    case vpiAssertionKill:
      s.attempts.erase(attempt_start_time);
      return true;
    case vpiAssertionDisableStep: {
      auto it = s.attempts.find(attempt_start_time);
      if (it != s.attempts.end()) it->second.step_enabled = false;
      return true;
    }
    default:
      return false;
  }
}

bool AssertionApi::ControlStep(int control, std::string_view assertion,
                               uint64_t attempt_start_time, int step_control) {
  if (assertion.empty() || SystemRefusesControl()) return false;
  if (step_control != vpiAssertionClockSteps) return false;
  AssertionControlState& s = StateFor(assertion);
  if (s.locked && control != vpiAssertionUnlock) return false;

  switch (control) {
    case vpiAssertionEnableStep: {
      AttemptControlState& att = s.attempts[attempt_start_time];
      if (!att.started) att.step_enabled = true;
      return true;
    }
    default:
      return false;
  }
}

bool AssertionApi::AssertionEnabled(std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  return s ? s->enabled : true;
}

bool AssertionApi::AssertionLocked(std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  return s ? s->locked : false;
}

bool AssertionApi::AssertionPassActionEnabled(
    std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  if (!s) return true;
  return s->vacuous_action_enabled && s->nonvacuous_action_enabled;
}

bool AssertionApi::AssertionFailActionEnabled(
    std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  return s ? s->fail_action_enabled : true;
}

bool AssertionApi::AssertionVacuousActionEnabled(
    std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  return s ? s->vacuous_action_enabled : true;
}

bool AssertionApi::AssertionNonvacuousActionEnabled(
    std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  return s ? s->nonvacuous_action_enabled : true;
}

bool AssertionApi::AssertionStepEnabled(std::string_view assertion,
                                        uint64_t attempt_start_time) const {
  const AssertionControlState* s = FindState(assertion);
  if (!s) return false;
  auto it = s->attempts.find(attempt_start_time);
  return it != s->attempts.end() && it->second.step_enabled;
}

uint32_t AssertionApi::AssertionAttemptsInProgress(
    std::string_view assertion) const {
  const AssertionControlState* s = FindState(assertion);
  if (!s) return 0;
  uint32_t count = 0;
  for (const auto& [time, att] : s->attempts) {
    if (att.started) ++count;
  }
  return count;
}

void AssertionApi::NoteAssertionAttemptStarted(std::string_view assertion,
                                               uint64_t attempt_start_time) {
  if (assertion.empty()) return;
  StateFor(assertion).attempts[attempt_start_time].started = true;
}

uint32_t AssertionApi::TakeAttemptStep(std::string_view assertion,
                                       uint64_t attempt_start_time) {
  auto state = assertion_state_.find(std::string(assertion));
  if (state == assertion_state_.end()) return kNoStep;
  auto it = state->second.attempts.find(attempt_start_time);
  if (it == state->second.attempts.end() || !it->second.started ||
      !it->second.step_enabled) {
    return kNoStep;
  }
  return it->second.steps++;
}

}  // namespace delta
