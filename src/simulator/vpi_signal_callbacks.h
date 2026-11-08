#pragma once

#include <vector>

#include "simulator/vpi_user.h"

namespace delta {

void VpiTrapSignal(int signal);
void VpiReleaseSignal(int signal, const std::vector<s_cb_data>& callbacks);
std::vector<int> VpiTakeRaisedSignals();

}  // namespace delta
