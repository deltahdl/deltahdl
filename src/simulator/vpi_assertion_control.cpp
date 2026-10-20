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

// §39.5.2: the attempt start time reaches vpi_control() as a pointer to an
// s_vpi_time structure, and the model keeps an attempt's start as the one
// 64-bit count the two halves of that structure spell. A caller that passed no
// structure named no attempt, which is the zero attempt the model rejects.
std::uint64_t VpiAssertionAttemptStart(const s_vpi_time* time) {
  if (time == nullptr) return 0;
  return (static_cast<std::uint64_t>(time->high) << 32) |
         static_cast<std::uint64_t>(time->low);
}

// §39.5.2: these controls take a handle to an assertion statement, and a
// sequence or property instance is not one. A handle that is neither names
// nothing this control can act on, and the assertion the model acts on is the
// one instance that handle names (§39.3.1), kept under `key`.
bool VpiAssertionControlTarget(VpiHandle assertion, std::string& key) {
  if (assertion == nullptr) return false;
  if (!AssertionApi::IsAssertionStatementHandle(assertion->type)) return false;
  key = VpiAssertionKeyOf(*assertion);
  return true;
}

// §39.4.1 and §39.4.2: the callback reason that reports the control action
// `operation` performs -- the assertion system callback of a §39.5.1 control,
// the assertion callback of a §39.5.2 one -- and, §39.5.1 and §39.5.2, the
// §20.11 control types (Table 20-5) it amounts to in the run, applied in
// order: an end is a kill the assertions stay locked after, and a reset a
// kill followed by the controls that put the assertions back as they were
// at the outset. A step control has no row: no callback reports it, and the
// run has no part in it; neither has vpiAssertionKill's one attempt, which
// the run discards apart.
using enum AssertControlType;
struct ControlAction {
  int operation;
  int reason;
  std::array<AssertControlType, 4> run;
  size_t run_count;
};
constexpr ControlAction kControlActions[] = {
    {vpiAssertionSysLock, cbAssertionSysLock, {kLock}, 1},
    {vpiAssertionSysUnlock, cbAssertionSysUnlock, {kUnlock}, 1},
    {vpiAssertionSysOn, cbAssertionSysOn, {kOn}, 1},
    {vpiAssertionSysOff, cbAssertionSysOff, {kOff}, 1},
    {vpiAssertionSysKill, cbAssertionSysKill, {kKill}, 1},
    {vpiAssertionSysEnd, cbAssertionSysEnd, {kKill, kLock}, 2},
    {vpiAssertionSysReset,
     cbAssertionSysReset,
     {kKill, kOn, kPassOn, kFailOn},
     4},
    {vpiAssertionSysDisablePassAction,
     cbAssertionSysDisablePassAction,
     {kPassOff},
     1},
    {vpiAssertionSysEnablePassAction,
     cbAssertionSysEnablePassAction,
     {kPassOn},
     1},
    {vpiAssertionSysDisableFailAction,
     cbAssertionSysDisableFailAction,
     {kFailOff},
     1},
    {vpiAssertionSysEnableFailAction,
     cbAssertionSysEnableFailAction,
     {kFailOn},
     1},
    {vpiAssertionSysDisableVacuousAction,
     cbAssertionSysDisableVacuousAction,
     {kVacuousOff},
     1},
    {vpiAssertionSysEnableNonvacuousAction,
     cbAssertionSysEnableNonvacuousAction,
     {kNonvacuousOn},
     1},
    {vpiAssertionReset, cbAssertionReset, {kKill, kOn, kPassOn, kFailOn}, 4},
    {vpiAssertionLock, cbAssertionLock, {kLock}, 1},
    {vpiAssertionUnlock, cbAssertionUnlock, {kUnlock}, 1},
    {vpiAssertionDisable, cbAssertionDisable, {kOff}, 1},
    {vpiAssertionEnable, cbAssertionEnable, {kOn}, 1},
    {vpiAssertionKill, cbAssertionKill, {}, 0},
    {vpiAssertionDisablePassAction,
     cbAssertionDisablePassAction,
     {kPassOff},
     1},
    {vpiAssertionEnablePassAction, cbAssertionEnablePassAction, {kPassOn}, 1},
    {vpiAssertionDisableFailAction,
     cbAssertionDisableFailAction,
     {kFailOff},
     1},
    {vpiAssertionEnableFailAction, cbAssertionEnableFailAction, {kFailOn}, 1},
    {vpiAssertionDisableVacuousAction,
     cbAssertionDisableVacuousAction,
     {kVacuousOff},
     1},
    {vpiAssertionEnableNonvacuousAction,
     cbAssertionEnableNonvacuousAction,
     {kNonvacuousOn},
     1}};

int ReasonReporting(int operation) {
  const auto* found =
      std::find_if(std::begin(kControlActions), std::end(kControlActions),
                   [operation](const ControlAction& entry) {
                     return entry.operation == operation;
                   });
  return found == std::end(kControlActions) ? 0 : found->reason;
}

// §39.4.2 detail c: a control callback's cb_time is the time of the control
// action, the run's time now.
std::uint64_t ControlTime() {
  s_vpi_time now = {};
  now.type = vpiSimTime;
  GetGlobalVpiContext().GetTime(nullptr, &now);
  return (static_cast<std::uint64_t>(now.high) << 32) | now.low;
}

// §39.4.2: the assertion callbacks of the control action `operation` has
// just performed on the assertion `name`, called with no attempt
// information, and, §39.4.2.1, in a run as the run raises its own control
// callbacks; an operation that failed performed none.
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

// §39.5: the assertion types (Table 20-6) a VPI control acts on, the
// concurrent and the immediate assertions; neither an expect statement nor a
// violation report is an assertion Clause 39 reaches.
constexpr uint32_t kVpiControlledTypes =
    static_cast<uint32_t>(AssertionTypeBit::kConcurrent) |
    static_cast<uint32_t>(AssertionTypeBit::kSimpleImmediate) |
    static_cast<uint32_t>(AssertionTypeBit::kObservedDeferredImmediate) |
    static_cast<uint32_t>(AssertionTypeBit::kFinalDeferredImmediate);

// §39.5.1 and §39.5.2: the control action `operation` acting on the run the
// model is attached to, on every assertion where `selected` is empty and
// otherwise on those the one name it holds selects -- a scope's assertions,
// or the one assertion a key names -- as the §20.11 calls it amounts to, a
// kill aborting the attempts in flight of those it selects. Nothing where no
// run is attached.
void ActOnRun(int operation, std::string_view selected) {
  SimContext* run = GetGlobalVpiContext().Run();
  if (run == nullptr) return;
  for (const ControlAction& action : kControlActions) {
    if (action.operation != operation) continue;
    for (size_t i = 0; i < action.run_count; ++i) {
      AssertControlCall call;
      call.control_type = static_cast<uint32_t>(action.run[i]);
      call.assertion_type = kVpiControlledTypes;
      call.directive_type = kDirectiveTypeDefault;
      if (!selected.empty()) call.scopes.push_back({std::string(selected)});
      if (action.run[i] == kKill) AbortKilledAttempts(call, *run);
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
  // §39.5.1: the scope handle is what the control is confined to, and a null
  // handle is the whole of the design rather than a missing argument. A scope
  // object carries the name the model confines the control by.
  std::string_view name = scope != nullptr ? scope->name : std::string_view();
  if (!GetGlobalAssertionApi().SysControl(operation, name)) return 0;
  ActOnRun(operation, scope != nullptr ? std::string_view(scope->full_name)
                                       : std::string_view());
  // §39.4.1: the control action is reported to the assertion system
  // callbacks of its kind.
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
