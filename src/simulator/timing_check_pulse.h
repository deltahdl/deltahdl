#pragma once

#include <cstddef>

namespace delta {

class SimContext;
class SpecifyManager;

// Arms the watchers one of the three checks bounded by two edges of the
// reference signal needs: §31.4.4's $width, §31.4.5's $period and §31.4.6's
// $nochange. `index` is a position in SpecifyManager::GetTimingChecks, and the
// entry there has to be one of those three kinds.
//
// These differ from §31.3's stability windows in what closes the window.
// §31.3's checks bound a window with one edge of the reference signal and
// measure a transition of the data signal against it, so a watcher there needs
// one edge of each of two signals. §31.4.4 and §31.4.5 name one signal only and
// measure between consecutive edges of it, so the state a watcher carries is
// the time of the previous matching edge rather than a time taken from another
// signal. §31.4.6 names two, and bounds its window with both edges of the
// reference rather than one.
//
// Nothing is armed when a signal the check names is no variable of the design,
// which is what a check whose specify block was registered for a module the
// design never elaborated leaves behind.
void ArmPulseWindow(const SpecifyManager& mgr, std::size_t index,
                    SimContext& ctx);

}  // namespace delta
