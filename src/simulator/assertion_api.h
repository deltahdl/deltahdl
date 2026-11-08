#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulator/coverage_control.h"
#include "simulator/sva_engine_sequences.h"

namespace delta {

enum class AssertionAction : uint8_t {
  kNone = 0,
  kPass = 1,
  kFail = 2,
  kDisable = 3,
  kEnable = 4,
  kReset = 5,
  kKill = 6,
};

struct AssertionCbData {
  int reason = 0;
  AssertionSeverity severity = AssertionSeverity::kError;
  AssertionAction action = AssertionAction::kNone;
  std::string_view assertion_name;
  void* user_data = nullptr;
};

using AssertionCbFunc = std::function<void(const AssertionCbData&)>;

struct AssertionStepDetail {
  std::vector<std::string> matched_exprs;
  int state_from = 0;
  int state_to = 0;
};

struct AssertionAttemptInfo {
  uint64_t attempt_start_time = 0;
  std::string fail_expr;
  AssertionStepDetail step;
};

struct AssertionCallbackArgs {
  int reason = 0;
  uint64_t cb_time = 0;
  std::string assertion;
  const AssertionAttemptInfo* info = nullptr;
  void* user_data = nullptr;
};

using AssertionPlacedCallback =
    std::function<void(const AssertionCallbackArgs&)>;

using AssertionCallbackHandle = uint64_t;

std::string AssertionKey(std::string_view scope, std::string_view name,
                         uint32_t line, uint32_t column);

struct AssertionControlTarget {
  uint32_t type_bit = 0;
  uint32_t directive_bit = 0;
  std::string scope;
  std::string full_name;
};

constexpr int kCbAssertionStart = 601;
constexpr int kCbAssertionSuccess = 602;
constexpr int kCbAssertionFailure = 603;
constexpr int kCbAssertionDisabled = 604;
constexpr int kCbAssertionReset = 605;
constexpr int kCbAssertionKilled = 606;

class AssertionApi {
 public:
  void RegisterCallback(int reason, AssertionCbFunc cb, void* user_data);
  void FireCallback(const AssertionCbData& data);
  uint32_t CallbackCount() const;

  static bool IsAssertionCallbackReason(int reason);

  static bool IsAssertionSysCallbackReason(int reason);

  static bool IsReasonValidForHandle(int reason, int handle_type);

  static bool ReasonCarriesAttemptInfo(int reason);

  static bool IsValidFailingStep(const AssertionStepDetail& step);

  AssertionCallbackHandle PlaceAssertionCallback(int reason,
                                                 std::string_view assertion,
                                                 int handle_type,
                                                 AssertionPlacedCallback cb,
                                                 void* user_data);

  bool RemoveAssertionCallback(AssertionCallbackHandle handle);

  uint32_t PlacedCallbackCount() const;

  uint32_t DeliverAssertionEvent(std::string_view assertion, int reason,
                                 uint64_t cb_time,
                                 const AssertionAttemptInfo& info);

  void SetGlobalClockTicks(std::vector<uint64_t> ticks);

  void MarkAssertionUsesGlobalClockingFuture(std::string_view assertion);
  bool AssertionUsesGlobalClockingFuture(std::string_view assertion) const;

  static constexpr uint64_t kNoGlobalClockTick = UINT64_MAX;

  static uint64_t NearestGlobalClockTickAfter(
      const std::vector<uint64_t>& ticks, uint64_t event_time);

  uint32_t DeliverAssertionEventAtGlobalClock(std::string_view assertion,
                                              int reason, uint64_t event_time,
                                              const AssertionAttemptInfo& info);

  uint32_t AdvanceGlobalClockTick(uint64_t tick_time);

  uint32_t PendingGlobalClockingCallbackCount() const;

  void SetSeverity(std::string_view name, AssertionSeverity sev);
  AssertionSeverity GetSeverity(std::string_view name) const;

  void SetAction(std::string_view name, AssertionAction action);
  AssertionAction GetAction(std::string_view name) const;

  bool SysControl(int control, std::string_view scope = {});

  static bool IsAssertionStatementHandle(int vpi_type);

  bool Control(int control, std::string_view assertion);

  bool ControlAttempt(int control, std::string_view assertion,
                      uint64_t attempt_start_time);

  bool ControlStep(int control, std::string_view assertion,
                   uint64_t attempt_start_time, int step_control);

  bool AssertionEnabled(std::string_view assertion) const;
  bool AssertionLocked(std::string_view assertion) const;
  bool AssertionPassActionEnabled(std::string_view assertion) const;
  bool AssertionFailActionEnabled(std::string_view assertion) const;
  bool AssertionVacuousActionEnabled(std::string_view assertion) const;
  bool AssertionNonvacuousActionEnabled(std::string_view assertion) const;
  bool AssertionStepEnabled(std::string_view assertion,
                            uint64_t attempt_start_time) const;
  uint32_t AssertionAttemptsInProgress(std::string_view assertion) const;

  void NoteAssertionAttemptStarted(std::string_view assertion,
                                   uint64_t attempt_start_time);

  static constexpr uint32_t kNoStep = UINT32_MAX;
  uint32_t TakeAttemptStep(std::string_view assertion,
                           uint64_t attempt_start_time);

  bool LastControlGlobal() const { return last_control_global_; }
  bool AssertionsStarted() const { return started_; }
  bool SysLocked() const { return locked_; }
  bool SysEnded() const { return ended_; }
  bool PassActionEnabled() const {
    return vacuous_action_enabled_ && nonvacuous_action_enabled_;
  }
  bool FailActionEnabled() const { return fail_action_enabled_; }
  bool VacuousActionEnabled() const { return vacuous_action_enabled_; }
  bool NonvacuousActionEnabled() const { return nonvacuous_action_enabled_; }
  uint32_t AttemptsInProgress() const { return attempts_in_progress_; }

  void NoteAttemptStarted() { ++attempts_in_progress_; }

  void QueuePendingAssertionReport(std::string_view assertion);

  uint32_t PendingAssertionReportCount(std::string_view assertion) const;

  void NoteControlTarget(std::string_view assertion,
                         AssertionControlTarget target);
  const std::map<std::string, AssertionControlTarget, std::less<>>&
  ControlTargets() const {
    return control_targets_;
  }

 private:
  struct CbEntry {
    int reason = 0;
    AssertionCbFunc cb;
    void* user_data = nullptr;
  };
  std::vector<CbEntry> callbacks_;

  struct PlacedCb {
    AssertionCallbackHandle handle = 0;
    int reason = 0;
    std::string assertion;
    AssertionPlacedCallback cb;
    void* user_data = nullptr;
  };
  std::vector<PlacedCb> placed_callbacks_;
  std::map<std::string, AssertionControlTarget, std::less<>> control_targets_;
  AssertionCallbackHandle next_callback_handle_ = 1;

  struct PendingGlobalClockingCb {
    std::string assertion;
    int reason = 0;
    uint64_t event_time = 0;
    uint64_t delivery_time = 0;
    AssertionAttemptInfo info;
  };
  std::vector<PendingGlobalClockingCb> pending_global_clocking_cbs_;
  std::vector<uint64_t> global_clock_ticks_;
  std::unordered_set<std::string> global_clocking_future_assertions_;

  std::unordered_map<std::string, AssertionSeverity> severity_map_;
  std::unordered_map<std::string, AssertionAction> action_map_;

  bool started_ = true;
  bool locked_ = false;
  bool ended_ = false;
  bool fail_action_enabled_ = true;
  bool vacuous_action_enabled_ = true;
  bool nonvacuous_action_enabled_ = true;
  uint32_t attempts_in_progress_ = 0;
  bool last_control_global_ = false;

  struct AttemptControlState {
    bool started = false;
    bool step_enabled = false;
    uint32_t steps = 0;
  };
  struct AssertionControlState {
    bool enabled = true;
    bool locked = false;
    bool fail_action_enabled = true;
    bool vacuous_action_enabled = true;
    bool nonvacuous_action_enabled = true;
    std::unordered_map<uint64_t, AttemptControlState> attempts;
  };
  std::unordered_map<std::string, AssertionControlState> assertion_state_;
  AssertionControlState& StateFor(std::string_view assertion);
  bool SystemRefusesControl() const { return locked_ || ended_; }
  const AssertionControlState* FindState(std::string_view assertion) const;

  std::unordered_map<std::string, uint32_t> pending_assertion_reports_;
  void FlushPendingAssertionReports(std::string_view assertion);
  void FlushAllPendingAssertionReports();
};

AssertionApi& GetGlobalAssertionApi();
void SetGlobalAssertionApi(AssertionApi* api);

class CoverageApi {
 public:
  void SetControl(CoverageControl ctrl);
  CoverageControl GetControl() const;

  void SetMaxBins(uint32_t max_bins);
  uint32_t GetMaxBins() const;

  void SetActive(bool active);
  bool IsActive() const;

  void StoreValue(std::string_view key, double value);
  double GetValue(std::string_view key) const;

 private:
  CoverageControl control_ = CoverageControl::kStart;
  uint32_t max_bins_ = 64;
  bool active_ = true;
  std::unordered_map<std::string, double> values_;
};

}  // namespace delta
