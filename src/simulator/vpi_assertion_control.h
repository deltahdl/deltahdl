#pragma once

// §39.5: the control functions of the assertion API - "how to obtain assertion
// system control and assertion control information". Each is a vpi_control()
// operation whose arguments §39.5.1 and §39.5.2 fix, and each acts on the
// assertion model of simulator/dpi_runtime.h, so the reading of the arguments
// stands here between vpi_control() and that model.

#include "simulator/dpi_runtime.h"
#include "simulator/sv_vpi_user.h"

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

// §39.5.1: "To control the assertion system, use vpi_control() with one of the
// following constants and a second handle argument that is a vpiHandle for a
// scope. A NULL handle signifies that the control applies to all assertions
// regardless of scope." 1 where the control was applied, 0 where it was not.
PLI_INT32 VpiAssertionSysControl(int operation, VpiHandle scope);

// §39.5.2: the second argument "shall be a valid assertion handle", and "only
// assertion statement handles are valid here, not sequence or property
// instances". 1 where the control was applied, 0 where it was not.
PLI_INT32 VpiAssertionControl(int operation, VpiHandle assertion);

// §39.5.2: with the attempt start time as the third argument, "as a pointer to
// a correctly initialized s_vpi_time structure" - vpiAssertionKill, which
// discards the given attempt, and vpiAssertionDisableStep.
PLI_INT32 VpiAssertionAttemptControl(int operation, VpiHandle assertion,
                                     const VpiTime* attempt_start_time);

// §39.5.2: vpiAssertionEnableStep, whose fourth argument "shall be a step
// control constant" - vpiAssertionClockSteps, the per-assertion/clock-tick
// stepping the clause defines.
PLI_INT32 VpiAssertionStepControl(int operation, VpiHandle assertion,
                                  const VpiTime* attempt_start_time,
                                  int step_control);

}  // namespace delta
