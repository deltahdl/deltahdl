#include "simulator/vpi_assertion_control.h"

#include <cstdint>
#include <string_view>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §39.5.2: the attempt start time reaches vpi_control() as a pointer to an
// s_vpi_time structure, and the model keeps an attempt's start as the one
// 64-bit count the two halves of that structure spell. A caller that passed no
// structure named no attempt, which is the zero attempt the model rejects.
std::uint64_t VpiAssertionAttemptStart(const VpiTime* time) {
  if (time == nullptr) return 0;
  return (static_cast<std::uint64_t>(time->high) << 32) |
         static_cast<std::uint64_t>(time->low);
}

// §39.5.2: "Only assertion statement handles are valid here, not sequence or
// property instances." A handle that is neither names nothing this control can
// act on, and the assertion the model acts on is named by that handle.
bool VpiAssertionControlTarget(VpiHandle assertion, std::string_view& name) {
  if (assertion == nullptr) return false;
  if (!AssertionApi::IsAssertionStatementHandle(assertion->type)) return false;
  name = assertion->name;
  return !name.empty();
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
  return GetGlobalAssertionApi().SysControl(operation, name) ? 1 : 0;
}

PLI_INT32 VpiAssertionControl(int operation, VpiHandle assertion) {
  std::string_view name;
  if (!VpiAssertionControlTarget(assertion, name)) return 0;
  return GetGlobalAssertionApi().Control(operation, name) ? 1 : 0;
}

PLI_INT32 VpiAssertionAttemptControl(int operation, VpiHandle assertion,
                                     const VpiTime* attempt_start_time) {
  std::string_view name;
  if (!VpiAssertionControlTarget(assertion, name)) return 0;
  return GetGlobalAssertionApi().ControlAttempt(
             operation, name, VpiAssertionAttemptStart(attempt_start_time))
             ? 1
             : 0;
}

PLI_INT32 VpiAssertionStepControl(int operation, VpiHandle assertion,
                                  const VpiTime* attempt_start_time,
                                  int step_control) {
  std::string_view name;
  if (!VpiAssertionControlTarget(assertion, name)) return 0;
  return GetGlobalAssertionApi().ControlStep(
             operation, name, VpiAssertionAttemptStart(attempt_start_time),
             step_control)
             ? 1
             : 0;
}

}  // namespace delta
