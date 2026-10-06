#pragma once

// §39.5: the control functions of the assertion API, which control the
// assertion system and single assertions. Each is a vpi_control()
// operation whose arguments §39.5.1 and §39.5.2 fix, and each acts on the
// assertion model of simulator/dpi_runtime.h, so the reading of the arguments
// stands here between vpi_control() and that model.

#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

// §39.5.1: whether `operation` is one of the assertion system controls, and
// §39.5.2: whether it is one of the per-assertion controls taking the assertion
// handle alone, one of the two taking an attempt start time as well, or the
// enable-step control that takes a step control constant on top of that.
// vpi_control() reads a different argument list for each, so it asks first.
bool VpiIsAssertionSysControl(int operation);
bool VpiIsAssertionControl(int operation);
bool VpiIsAssertionAttemptControl(int operation);
bool VpiIsAssertionStepControl(int operation);

// §39.5.1: the assertion system is controlled by vpi_control() with one of the
// clause's constants and a scope handle, a NULL handle applying the control to
// every assertion whatever its scope. 1 where the control was applied, 0 where
// it was not.
PLI_INT32 VpiAssertionSysControl(int operation, VpiHandle scope);

// §39.5.2: the second argument has to be a valid handle to an assertion
// statement, and a sequence or property instance is not one. 1 where the
// control was applied, 0 where it was not.
PLI_INT32 VpiAssertionControl(int operation, VpiHandle assertion);

// §39.5.2: with the attempt start time as the third argument, given as a
// pointer to an s_vpi_time structure initialized for it - vpiAssertionKill,
// which discards the given attempt, and vpiAssertionDisableStep.
PLI_INT32 VpiAssertionAttemptControl(int operation, VpiHandle assertion,
                                     const s_vpi_time* attempt_start_time);

// §39.5.2: vpiAssertionEnableStep, whose fourth argument has to be one of the
// step control constants - vpiAssertionClockSteps, the per-assertion/clock-tick
// stepping the clause defines.
PLI_INT32 VpiAssertionStepControl(int operation, VpiHandle assertion,
                                  const s_vpi_time* attempt_start_time,
                                  int step_control);

}  // namespace delta
