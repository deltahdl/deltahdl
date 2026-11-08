#pragma once

#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

bool VpiIsAssertionSysControl(int operation);
bool VpiIsAssertionControl(int operation);
bool VpiIsAssertionAttemptControl(int operation);
bool VpiIsAssertionStepControl(int operation);

PLI_INT32 VpiAssertionSysControl(int operation, VpiHandle scope);

PLI_INT32 VpiAssertionControl(int operation, VpiHandle assertion);

PLI_INT32 VpiAssertionAttemptControl(int operation, VpiHandle assertion,
                                     const s_vpi_time* attempt_start_time);

PLI_INT32 VpiAssertionStepControl(int operation, VpiHandle assertion,
                                  const s_vpi_time* attempt_start_time,
                                  int step_control);

void VpiStartAssertionSystem();
void VpiEndAssertionSystem();

}  // namespace delta
