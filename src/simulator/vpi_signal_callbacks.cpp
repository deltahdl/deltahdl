#include "simulator/vpi_signal_callbacks.h"

#include <algorithm>
#include <array>
#include <csignal>
#include <cstddef>
#include <vector>

#include "simulator/vpi_context.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The signals a trap can record, numbered from 0.
constexpr int kSignalSlots = 65;

volatile std::sig_atomic_t g_raised[kSignalSlots] = {};
volatile std::sig_atomic_t g_any_raised = 0;

using SignalHandler = void (*)(int);

struct Trap {
  bool trapped = false;
  SignalHandler previous = SIG_DFL;
};

std::array<Trap, kSignalSlots>& Traps() {
  static std::array<Trap, kSignalSlots> traps;
  return traps;
}

bool InRange(int signal) { return signal > 0 && signal < kSignalSlots; }

}  // namespace

}  // namespace delta

extern "C" {
static void RecordVpiSignal(int signal) {
  if (signal > 0 && signal < delta::kSignalSlots) {
    delta::g_raised[signal] = 1;
    delta::g_any_raised = 1;
  }
}
}

namespace delta {

void VpiTrapSignal(int signal) {
  if (!InRange(signal) || Traps()[signal].trapped) return;
  SignalHandler previous = std::signal(signal, &RecordVpiSignal);
  if (previous == SIG_ERR) return;
  Traps()[signal] = {true, previous};
}

void VpiReleaseSignal(int signal, const std::vector<s_cb_data>& callbacks) {
  if (!InRange(signal) || !Traps()[signal].trapped) return;
  const bool kStillAsked =
      std::ranges::any_of(callbacks, [signal](const s_cb_data& cb) {
        return cb.reason == cbSignal && cb.index == signal;
      });
  if (kStillAsked) return;
  std::signal(signal, Traps()[signal].previous);
  Traps()[signal] = {};
}

std::vector<int> VpiTakeRaisedSignals() {
  std::vector<int> raised;
  if (g_any_raised == 0) return raised;
  g_any_raised = 0;
  for (int signal = 1; signal < kSignalSlots; ++signal) {
    if (g_raised[signal] == 0) continue;
    g_raised[signal] = 0;
    raised.push_back(signal);
  }
  return raised;
}

int VpiContext::DeliverRaisedSignals() {
  int fired = 0;
  for (const int kSignal : VpiTakeRaisedSignals()) {
    const std::size_t kCount = callbacks_.size();
    for (std::size_t i = 0; i < kCount; ++i) {
      if (callbacks_[i].reason != cbSignal || callbacks_[i].index != kSignal ||
          callbacks_[i].cb_rtn == nullptr) {
        continue;
      }
      Deliver(callbacks_[i]);
      ++fired;
    }
  }
  return fired;
}

}  // namespace delta
