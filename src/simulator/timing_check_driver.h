#pragma once

namespace delta {

class SimContext;
class SpecifyManager;

// Clause 31's timing checks, evaluated against a running design. A check
// SpecifyManager holds is a declaration and nothing else until something
// watches the signals it names, so a design that writes $setup or $hold has its
// violation reported and its notifier toggled only once this has been called.
//
// WatchTimingChecks arms, for every $setup and every $hold entry
// SpecifyManager::GetTimingChecks holds, one watcher on each of the two signals
// that check names. §31.3 gives both the same three steps -- "define a time
// window with respect to the reference signal using the specified limit or
// limits", "check the time of transition of the data signal with respect to the
// time window", and "report a timing violation if the data signal transitions
// within the time window" -- and Table 31-1 and Table 31-2 say which of the two
// signals is the timestamp event and which is the timecheck event. §31.3.1 and
// §31.3.2 write both end points of the window in terms of the timecheck time
// and place the timestamp time inside it, so the transition that closes a
// window is the timecheck event: the reference signal for $setup and the data
// signal for $hold, which Syntax 31-3 and Syntax 31-4 both write as the check's
// second argument. The watcher on the timestamp signal records when that signal
// last made the transition the check was written with, and the watcher on the
// timecheck signal is where the comparison happens.
//
// A violation is reported through SimContext::GetDiag as a warning, and toggles
// the check's notifier when it names one, which §31.6 makes the design-visible
// half of a violation.
//
// Only §31.3's $setup and $hold are armed. $setuphold, $recovery, $removal and
// $recrem stand in the same subclause and are not, nor are §31.4's clock and
// control-signal checks, §31.4.4's $width, §31.4.5's $period or §31.9's
// negative timing checks; each names its two transitions differently and needs
// reading against its own clause.
//
// Call this after every module has been lowered and before the scheduler runs
// anything, beside WatchModulePathSources (src/simulator/module_path_delay.h):
// a signal that transitions before it is watched leaves no transition behind
// for the check to measure. Lowerer::RegisterDesignTiming
// (src/simulator/lowerer.cpp) is that point. `mgr` has to outlive the run,
// because each watcher reads the entry it was armed for back out of it at every
// timecheck event; SimContext::AcquireSpecifyManager gives a manager the
// context owns, which does.
void WatchTimingChecks(const SpecifyManager& mgr, SimContext& ctx);

}  // namespace delta
