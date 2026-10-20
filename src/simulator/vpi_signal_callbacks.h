#pragma once

#include <vector>

#include "simulator/vpi_user.h"

namespace delta {

// §38.36.3: a cbSignal callback asks the tool to trap the operating system's
// signal its index names. The trap records the signal and nothing else; the
// callbacks are called at the run's next safe point (VpiContext::
// DeliverRaisedSignals), where any VPI routine may be called.

// Traps `signal`, the previous handler kept for VpiReleaseSignal.
void VpiTrapSignal(int signal);
// Restores the handler `signal` had before VpiTrapSignal where no live
// cbSignal among `callbacks` asks for it any longer.
void VpiReleaseSignal(int signal, const std::vector<s_cb_data>& callbacks);
// Hands back the signals trapped since the last call, clearing them.
std::vector<int> VpiTakeRaisedSignals();

}  // namespace delta
