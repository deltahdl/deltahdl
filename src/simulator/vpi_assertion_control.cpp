#include "simulator/vpi_assertion_control.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string>
#include <string_view>
#include <utility>

#include "simulator/assert_control_log.h"
#include "simulator/assertion_api.h"
#include "simulator/assertion_attempt_events.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_assertion_internal.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/vpi_assertion_cb.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::uint64_t VpiAssertionAttemptStart(const s_vpi_time* time) {
  if (time == nullptr) return 0;
  return (static_cast<std::uint64_t>(time->high) << 32) |
         static_cast<std::uint64_t>(time->low);
}

bool VpiAssertionControlTarget(VpiHandle assertion, std::string& key) {
  if (assertion == nullptr) return false;
  if (!AssertionApi::IsAssertionStatementHandle(assertion->type)) return false;
  key = VpiAssertionKeyOf(*assertion);
  return true;
}

using enum AssertControlType;
constexpr uint32_t CallType(AssertControlType type) {
  return static_cast<uint32_t>(type);
}
struct ControlAction {
  int operation;
  int reason;
  std::array<uint32_t, 4> run;
  size_t run_count;
};
constexpr ControlAction kControlActions[] = {
    {vpiAssertionSysLock, cbAssertionSysLock, {CallType(kLock)}, 1},
    {vpiAssertionSysUnlock, cbAssertionSysUnlock, {CallType(kUnlock)}, 1},
    {vpiAssertionSysOn, cbAssertionSysOn, {CallType(kOn)}, 1},
    {vpiAssertionSysOff, cbAssertionSysOff, {CallType(kOff)}, 1},
    {vpiAssertionSysKill, cbAssertionSysKill, {CallType(kKill)}, 1},
    {vpiAssertionSysEnd,
     cbAssertionSysEnd,
     {CallType(kKill), CallType(kLock)},
     2},
    {vpiAssertionSysReset,
     cbAssertionSysReset,
     {CallType(kKill), CallType(kOn), CallType(kPassOn), CallType(kFailOn)},
     4},
    {vpiAssertionSysDisablePassAction,
     cbAssertionSysDisablePassAction,
     {CallType(kPassOff)},
     1},
    {vpiAssertionSysEnablePassAction,
     cbAssertionSysEnablePassAction,
     {CallType(kPassOn)},
     1},
    {vpiAssertionSysDisableFailAction,
     cbAssertionSysDisableFailAction,
     {CallType(kFailOff)},
     1},
    {vpiAssertionSysEnableFailAction,
     cbAssertionSysEnableFailAction,
     {CallType(kFailOn)},
     1},
    {vpiAssertionSysDisableVacuousAction,
     cbAssertionSysDisableVacuousAction,
     {CallType(kVacuousOff)},
     1},
    {vpiAssertionSysEnableNonvacuousAction,
     cbAssertionSysEnableNonvacuousAction,
     {CallType(kNonvacuousOn)},
     1},
    {vpiAssertionReset,
     cbAssertionReset,
     {CallType(kKill), CallType(kOn), CallType(kPassOn), CallType(kFailOn)},
     4},
    {vpiAssertionLock, cbAssertionLock, {CallType(kLock)}, 1},
    {vpiAssertionUnlock, cbAssertionUnlock, {CallType(kUnlock)}, 1},
    {vpiAssertionDisable, cbAssertionDisable, {CallType(kOff)}, 1},
    {vpiAssertionEnable, cbAssertionEnable, {CallType(kOn)}, 1},
    {vpiAssertionKill, cbAssertionKill, {}, 0},
    {vpiAssertionDisablePassAction,
     cbAssertionDisablePassAction,
     {CallType(kPassOff)},
     1},
    {vpiAssertionEnablePassAction,
     cbAssertionEnablePassAction,
     {CallType(kPassOn)},
     1},
    {vpiAssertionDisableFailAction,
     cbAssertionDisableFailAction,
     {CallType(kFailOff)},
     1},
    {vpiAssertionEnableFailAction,
     cbAssertionEnableFailAction,
     {CallType(kFailOn)},
     1},
    {vpiAssertionDisableVacuousAction,
     cbAssertionDisableVacuousAction,
     {CallType(kVacuousOff)},
     1},
    {vpiAssertionEnableNonvacuousAction,
     cbAssertionEnableNonvacuousAction,
     {CallType(kNonvacuousOn)},
     1}};

int ReasonReporting(int operation) {
  const auto* found =
      std::find_if(std::begin(kControlActions), std::end(kControlActions),
                   [operation](const ControlAction& entry) {
                     return entry.operation == operation;
                   });
  return found == std::end(kControlActions) ? 0 : found->reason;
}

std::uint64_t ControlTime() {
  s_vpi_time now = {};
  now.type = vpiSimTime;
  GetGlobalVpiContext().GetTime(nullptr, &now);
  return (static_cast<std::uint64_t>(now.high) << 32) | now.low;
}

PLI_INT32 ReportAssertionControl(bool applied, int operation,
                                 std::string_view name) {
  if (!applied) return 0;
  int reason = ReasonReporting(operation);
  if (reason == 0) return 1;
  if (SimContext* run = GetGlobalVpiContext().Run()) {
    RaiseAssertionControlCallback(name, reason, *run);
  } else {
    GetGlobalAssertionApi().DeliverAssertionEvent(name, reason, ControlTime(),
                                                  {});
  }
  return 1;
}

constexpr uint32_t kVpiControlledTypes =
    static_cast<uint32_t>(AssertionTypeBit::kConcurrent) |
    static_cast<uint32_t>(AssertionTypeBit::kSimpleImmediate) |
    static_cast<uint32_t>(AssertionTypeBit::kObservedDeferredImmediate) |
    static_cast<uint32_t>(AssertionTypeBit::kFinalDeferredImmediate);

void ActOnRun(int operation, std::string_view selected) {
  SimContext* run = GetGlobalVpiContext().Run();
  if (run == nullptr) return;
  for (const ControlAction& action : kControlActions) {
    if (action.operation != operation) continue;
    for (size_t i = 0; i < action.run_count; ++i) {
      AssertControlCall call;
      call.control_type = action.run[i];
      call.assertion_type = kVpiControlledTypes;
      call.directive_type = kDirectiveTypeDefault;
      if (!selected.empty()) call.scopes.push_back({std::string(selected)});
      if (action.run[i] == CallType(kKill)) AbortKilledAttempts(call, *run);
      run->AssertControls().Apply(std::move(call));
    }
  }
}

}  // namespace

bool VpiIsAssertionSysControl(int operation) {
  switch (operation) {
    case vpiAssertionSysLock:
    case vpiAssertionSysUnlock:
    case vpiAssertionSysOn:
    case vpiAssertionSysOff:
    case vpiAssertionSysKill:
    case vpiAssertionSysEnd:
    case vpiAssertionSysReset:
    case vpiAssertionSysDisablePassAction:
    case vpiAssertionSysEnablePassAction:
    case vpiAssertionSysDisableFailAction:
    case vpiAssertionSysEnableFailAction:
    case vpiAssertionSysDisableVacuousAction:
    case vpiAssertionSysEnableNonvacuousAction:
      return true;
    default:
      return false;
  }
}

bool VpiIsAssertionControl(int operation) {
  switch (operation) {
    case vpiAssertionReset:
    case vpiAssertionLock:
    case vpiAssertionUnlock:
    case vpiAssertionDisable:
    case vpiAssertionEnable:
    case vpiAssertionDisablePassAction:
    case vpiAssertionEnablePassAction:
    case vpiAssertionDisableFailAction:
    case vpiAssertionEnableFailAction:
    case vpiAssertionDisableVacuousAction:
    case vpiAssertionEnableNonvacuousAction:
      return true;
    default:
      return false;
  }
}

bool VpiIsAssertionAttemptControl(int operation) {
  return operation == vpiAssertionKill || operation == vpiAssertionDisableStep;
}

bool VpiIsAssertionStepControl(int operation) {
  return operation == vpiAssertionEnableStep;
}

PLI_INT32 VpiAssertionSysControl(int operation, VpiHandle scope) {
  std::string_view name = scope != nullptr ? scope->name : std::string_view();
  if (!GetGlobalAssertionApi().SysControl(operation, name)) return 0;
  ActOnRun(operation, scope != nullptr ? std::string_view(scope->full_name)
                                       : std::string_view());
  GetGlobalVpiContext().DispatchCallbacks(ReasonReporting(operation));
  return 1;
}

PLI_INT32 VpiAssertionControl(int operation, VpiHandle assertion) {
  std::string name;
  if (!VpiAssertionControlTarget(assertion, name)) return 0;
  const bool kApplied = GetGlobalAssertionApi().Control(operation, name);
  if (kApplied) ActOnRun(operation, name);
  return ReportAssertionControl(kApplied, operation, name);
}

PLI_INT32 VpiAssertionAttemptControl(int operation, VpiHandle assertion,
                                     const s_vpi_time* attempt_start_time) {
  std::string name;
  if (!VpiAssertionControlTarget(assertion, name)) return 0;
  const std::uint64_t kStart = VpiAssertionAttemptStart(attempt_start_time);
  const bool kApplied =
      GetGlobalAssertionApi().ControlAttempt(operation, name, kStart);
  SimContext* run = GetGlobalVpiContext().Run();
  if (kApplied && operation == vpiAssertionKill && run != nullptr) {
    AbortAttemptStartedAt(name, kStart, *run);
  }
  return ReportAssertionControl(kApplied, operation, name);
}

PLI_INT32 VpiAssertionStepControl(int operation, VpiHandle assertion,
                                  const s_vpi_time* attempt_start_time,
                                  int step_control) {
  std::string name;
  if (!VpiAssertionControlTarget(assertion, name)) return 0;
  return GetGlobalAssertionApi().ControlStep(
             operation, name, VpiAssertionAttemptStart(attempt_start_time),
             step_control)
             ? 1
             : 0;
}

void VpiStartAssertionSystem() {
  VpiContext& vpi = GetGlobalVpiContext();
  vpi.DispatchCallbacks(cbAssertionSysInitialized);
  if (GetGlobalAssertionApi().AssertionsStarted()) {
    vpi.DispatchCallbacks(cbAssertionSysOn);
  }
}

void VpiEndAssertionSystem() {
  if (GetGlobalAssertionApi().SysEnded()) return;
  GetGlobalVpiContext().DispatchCallbacks(cbAssertionSysEnd);
}

}  // namespace delta
