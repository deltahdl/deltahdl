#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"

namespace delta {

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

// §39.4.2: the step callbacks. A single placed step callback covers both, so
// matching treats the two step reasons interchangeably.
bool IsStepReason(int reason) {
  return reason == cbAssertionStepSuccess || reason == cbAssertionStepFailure;
}

}  // namespace

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
  // Any assertion callback reason may be placed on a concurrent or immediate
  // assertion statement.
  if (IsAssertionStatementHandle(handle_type)) return true;
  // A sequence or property instance accepts only the start, success, and
  // failure callbacks.
  if (handle_type == vpiSequenceDecl || handle_type == vpiProperty ||
      handle_type == vpiPropertyDecl) {
    return reason == cbAssertionStart || reason == cbAssertionSuccess ||
           reason == cbAssertionFailure;
  }
  // No other handle type bears assertion callbacks.
  return false;
}

bool AssertionApi::ReasonCarriesAttemptInfo(int reason) {
  switch (reason) {
    // The control and action callbacks carry no attempt information.
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
  // An empty (null) handle, an unknown reason, or a reason that may not be
  // placed on this handle type is a placement error: return the NULL handle.
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

uint32_t AssertionApi::PlacedCallbackCount() const {
  return static_cast<uint32_t>(placed_callbacks_.size());
}

uint32_t AssertionApi::DeliverAssertionEvent(std::string_view assertion,
                                             int reason, uint64_t cb_time,
                                             const AssertionAttemptInfo& info) {
  // A failing step shall always carry at least one expression; a malformed one
  // is rejected and fires nothing.
  if (reason == cbAssertionStepFailure && !IsValidFailingStep(info.step)) {
    return 0;
  }

  AssertionCallbackArgs args;
  args.reason = reason;
  args.cb_time = cb_time;
  args.assertion = std::string(assertion);
  args.user_data = nullptr;
  // The attempt-info pointer is null for the reasons that carry no attempt
  // information; otherwise it points at the supplied attempt information.
  const AssertionAttemptInfo* info_ptr =
      ReasonCarriesAttemptInfo(reason) ? &info : nullptr;
  args.info = info_ptr;

  uint32_t fired = 0;
  for (auto& entry : placed_callbacks_) {
    if (std::string_view(entry.assertion) != assertion) continue;
    // A placed step callback is invoked for both success and failure steps;
    // every other reason matches exactly.
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
  // The nearest tick strictly following the event is the smallest tick greater
  // than it; a tick coinciding with the event does not qualify. The schedule
  // need not be sorted, so scan for the minimum qualifying tick.
  uint64_t nearest = kNoGlobalClockTick;
  for (uint64_t tick : ticks) {
    if (tick > event_time && tick < nearest) nearest = tick;
  }
  return nearest;
}

uint32_t AssertionApi::DeliverAssertionEventAtGlobalClock(
    std::string_view assertion, int reason, uint64_t event_time,
    const AssertionAttemptInfo& info) {
  // An assertion that does not refer to a global clocking future sampled value
  // function has no deferral: deliver at the event time as usual.
  if (!AssertionUsesGlobalClockingFuture(assertion)) {
    return DeliverAssertionEvent(assertion, reason, event_time, info);
  }
  // §39.4.2.1: defer delivery to the nearest global clock tick strictly
  // following the event. Nothing fires at the event time; the event time is
  // remembered so it can be reported as cb_time when the callback executes.
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
      // The deferred tick has been reached. Delivery reports the event time as
      // cb_time, not this later tick, and reuses the §39.4.2 delivery path.
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

// §39.5.1 system-wide flag bundle mutated by the §39.5.3 controls that discard
// attempts and reconfigure starting/actions. Holding references lets the
// control-case helpers below run without naming the private member set.
struct SysControlState {
  uint32_t& attempts_in_progress;
  bool& started;
  bool& ended;
  bool& fail_action_enabled;
  bool& vacuous_action_enabled;
  bool& nonvacuous_action_enabled;
};

// True for the two §39.4.2 step reasons removed by a system reset.
bool IsStepCallbackReason(int reason) {
  return reason == cbAssertionStepSuccess || reason == cbAssertionStepFailure;
}

// vpiAssertionSysReset: restore the system to its initial running state, drop
// the step success/failure callbacks, and leave all others installed. Templated
// on the callback container so the private CbEntry type need not be named.
template <typename CallbackVec>
void ApplySysReset(const SysControlState& s, CallbackVec& callbacks) {
  s.attempts_in_progress = 0;
  s.started = true;
  s.fail_action_enabled = true;
  s.vacuous_action_enabled = true;
  s.nonvacuous_action_enabled = true;
  std::erase_if(callbacks,
                [](const auto& e) { return IsStepCallbackReason(e.reason); });
}

// vpiAssertionSysKill: discard attempts in progress and disable further starts.
void ApplySysKill(const SysControlState& s) {
  s.attempts_in_progress = 0;
  s.started = false;
}

// vpiAssertionSysEnd: discard attempts, disable further starts, remove all
// installed callbacks, and mark the system ended so no further action proceeds.
template <typename CallbackVec>
void ApplySysEnd(const SysControlState& s, CallbackVec& callbacks) {
  s.attempts_in_progress = 0;
  s.started = false;
  s.ended = true;
  callbacks.clear();
}

}  // namespace

bool AssertionApi::SysControl(int control, std::string_view scope) {
  // Once the system has ended, no further assertion-related actions are
  // permitted.
  if (ended_) return false;
  // While locked, the status of the assertions cannot be changed; only an
  // unlock control may proceed.
  if (locked_ && control != vpiAssertionSysUnlock) return false;

  // An empty (null) scope means the control applies to all assertions
  // regardless of scope.
  last_control_global_ = scope.empty();

  const SysControlState state{attempts_in_progress_,
                              started_,
                              ended_,
                              fail_action_enabled_,
                              vacuous_action_enabled_,
                              nonvacuous_action_enabled_};

  switch (control) {
    case vpiAssertionSysReset:
      ApplySysReset(state, callbacks_);
      // §39.5.3: discarding all attempts in progress also flushes the
      // not-yet-matured deferred/procedural-concurrent instances of every
      // assertion.
      FlushAllPendingAssertionReports();
      return true;
    case vpiAssertionSysOff:
      // Disable further starts; attempts already executing are not affected.
      started_ = false;
      return true;
    case vpiAssertionSysKill:
      ApplySysKill(state);
      // §39.5.3: the discarded attempts' pending deferred/procedural-concurrent
      // instances are flushed along with them.
      FlushAllPendingAssertionReports();
      return true;
    case vpiAssertionSysLock:
      locked_ = true;
      return true;
    case vpiAssertionSysUnlock:
      locked_ = false;
      return true;
    case vpiAssertionSysOn:
      // Restart the system so attempts resume on all assertions.
      started_ = true;
      return true;
    case vpiAssertionSysEnd:
      ApplySysEnd(state, callbacks_);
      // §39.5.3: discarding all attempts in progress also flushes their pending
      // deferred/procedural-concurrent instances.
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
  // Assert/assume/cover statements (immediate or concurrent) are the only
  // handles these per-assertion controls accept. Sequence and property
  // instances are not valid targets.
  switch (vpi_type) {
    case vpiAssert:
    case vpiAssume:
    case vpiCover:
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
  // The second argument shall be a valid assertion handle.
  if (assertion.empty()) return false;
  AssertionControlState& s = StateFor(assertion);
  // While locked, the status of the assertion cannot be changed without first
  // unlocking it.
  if (s.locked && control != vpiAssertionUnlock) return false;

  switch (control) {
    case vpiAssertionReset:
      // Discard all attempts in progress for this assertion (which also clears
      // their per-attempt stepping) and restore it to its initial state.
      s.attempts.clear();
      s.enabled = true;
      s.fail_action_enabled = true;
      s.vacuous_action_enabled = true;
      s.nonvacuous_action_enabled = true;
      // §39.5.3: discarding current attempts also flushes any not-yet-matured
      // deferred/procedural-concurrent instances queued for this assertion.
      FlushPendingAssertionReports(assertion);
      return true;
    case vpiAssertionLock:
      s.locked = true;
      return true;
    case vpiAssertionUnlock:
      s.locked = false;
      return true;
    case vpiAssertionDisable:
      // Disable the starting of new attempts; existing attempts are unaffected.
      s.enabled = false;
      return true;
    case vpiAssertionEnable:
      s.enabled = true;
      return true;
    case vpiAssertionDisablePassAction:
      // Pass action covers both vacuous and nonvacuous success.
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
  if (assertion.empty()) return false;
  AssertionControlState& s = StateFor(assertion);
  if (s.locked && control != vpiAssertionUnlock) return false;

  switch (control) {
    case vpiAssertionKill:
      // Discard the given attempt (identified by its start time); the assertion
      // stays enabled and no state used by it (e.g., past() sampling) is reset.
      s.attempts.erase(attempt_start_time);
      return true;
    case vpiAssertionDisableStep: {
      // Disable step callbacks for the given attempt; no effect (idempotent)
      // when that attempt is not stepping or has no entry.
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
  if (assertion.empty()) return false;
  // The fourth argument shall be a step control constant.
  if (step_control != vpiAssertionClockSteps) return false;
  AssertionControlState& s = StateFor(assertion);
  if (s.locked && control != vpiAssertionUnlock) return false;

  switch (control) {
    case vpiAssertionEnableStep: {
      // Enable step callbacks for the given assertion attempt; stepping is
      // disabled by default for every attempt. The stepping mode can only be
      // set before the attempt has started: once it is in progress its mode is
      // frozen, so a later enable is accepted but has no effect.
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
  // Only attempts that have actually started count as in progress; an entry may
  // exist solely to hold a pre-start stepping configuration.
  uint32_t count = 0;
  for (const auto& [time, att] : s->attempts) {
    if (att.started) ++count;
  }
  return count;
}

void AssertionApi::NoteAssertionAttemptStarted(std::string_view assertion,
                                               uint64_t attempt_start_time) {
  if (assertion.empty()) return;
  // Mark the attempt started, preserving any stepping enabled for it ahead of
  // time. A brand-new entry has stepping disabled by default.
  StateFor(assertion).attempts[attempt_start_time].started = true;
}

}  // namespace delta
