// §31.3.1's $setup and §31.3.2's $hold, evaluated against a running design,
// and the dispatch that arms Clause 31's other ten checks.
// WatchTimingChecks, declared in simulator/timing_check_driver.h, is that
// dispatch: it reads each entry's kind and hands the entry to the file written
// for the shape that kind measures -- simulator/timing_check_stability.h for
// §31.3's remaining four, simulator/timing_check_pulse.h for §31.4.4, §31.4.5
// and §31.4.6, simulator/timing_check_skew.h for §31.4.1 through §31.4.3.
// simulator/timing_check_driver_internal.h holds what all four need: §31.5's
// edge matching, the watcher that arms on an edge, §31.2's report and §31.6's
// notifier.
//
// What is left here answers the one question a $setup or a $hold asks that the
// others do not: which transition of which signal closes the window, which
// §31.3.1's Table 31-1 and §31.3.2's Table 31-2 decide.
//
// SetupWindowViolated and HoldWindowViolated below restate the arithmetic of
// SpecifyManager::CheckSetupViolation and SpecifyManager::CheckHoldViolation
// (src/simulator/specify_timing_violation.cpp) from the two clauses those
// members read, rather than calling them. Both members select a check by the
// spelling of its signals -- `check.ref_signal != ref`, with no comparison of
// TimingCheckEntry::inst_prefix -- so with one check registered per module
// instance a single call answers for every instance of the cell, and answers
// true when any of them is violated. A watcher already knows which entry it was
// armed for, so it evaluates that entry and no other. Every file this dispatch
// reaches follows that rule for the same reason.

#include "simulator/timing_check_driver.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_specify.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/timing_check_driver_internal.h"
#include "simulator/timing_check_pulse.h"
#include "simulator/timing_check_skew.h"
#include "simulator/timing_check_stability.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// §31.3.1: "(beginning of time window) = (timecheck time) - limit" and "(end of
// time window) = (timecheck time)", and the check "reports a timing violation"
// when "(beginning of time window) < (timestamp time) < (end of time window)".
// The end points are not part of the violation region, which is also what makes
// a zero limit never issue a violation, as the clause states outright.
bool SetupWindowViolated(uint64_t limit, uint64_t timestamp_ticks,
                         uint64_t timecheck_ticks) {
  return timestamp_ticks < timecheck_ticks &&
         timecheck_ticks - timestamp_ticks < limit;
}

// §31.3.2: "(beginning of time window) = (timestamp time)" and "(end of time
// window) = (timestamp time) + limit", and the violation case is "(beginning of
// time window) <= (timecheck time) < (end of time window)". The window includes
// the end point it opens on and excludes the one it closes at, so a timecheck
// event at the timestamp time violates any nonzero limit.
bool HoldWindowViolated(uint64_t limit, uint64_t timestamp_ticks,
                        uint64_t timecheck_ticks) {
  return timecheck_ticks >= timestamp_ticks &&
         timecheck_ticks - timestamp_ticks < limit;
}

// Which of the two signals a §31.3 check names is its timestamp event and which
// is its timecheck event, each with the edge it was written with and qualified
// by the instance prefix the check was registered under.
struct StabilityWindowEvents {
  std::string timestamp_signal;
  SpecifyEdge timestamp_edge = SpecifyEdge::kNone;
  std::string timecheck_signal;
  SpecifyEdge timecheck_edge = SpecifyEdge::kNone;
};

// Table 31-1 makes $setup's data_event the timestamp event and its
// reference_event the timecheck event; Table 31-2 makes $hold's reference_event
// the timestamp event and its data_event the timecheck event. That is what
// decides which transition a check is evaluated on: §31.3.1 and §31.3.2 both
// write the end points of the window in terms of the timecheck time and place
// the timestamp time inside it, so the timecheck event's edge is what closes
// the window and the timestamp event's transition is what is measured against
// it. The reference signal closes a $setup window and the data signal closes a
// $hold one, which Syntax 31-3 and Syntax 31-4 both write as the check's second
// argument.
//
// The two fields are read by the names §31.3 gives them, so this depends on
// TimingCheckEntry::ref_signal carrying the reference_event of the declaration
// it was built from. Syntax 31-3 is the one check syntax of Clause 31 that
// writes the data event first, and Parser::ParseTimingCheck
// (src/parser/parser_specify.cpp) reads a check's two terminals positionally,
// so a $setup whose terminals are not put back in the fields named for them
// arrives with each in the other's; that is issue #3407, and a $setup evaluated
// here would measure the clock against the data signal's window rather than the
// other way round.
StabilityWindowEvents EventsOf(const TimingCheckEntry& check) {
  if (check.kind == TimingCheckKind::kSetup) {
    return StabilityWindowEvents{
        check.inst_prefix + check.data_signal, check.data_edge,
        check.inst_prefix + check.ref_signal, check.ref_edge};
  }
  return StabilityWindowEvents{
      check.inst_prefix + check.ref_signal, check.ref_edge,
      check.inst_prefix + check.data_signal, check.data_edge};
}

// One §31.3 check between the two transitions it measures: which entry it is,
// which two signals it measures between, and when its timestamp event last
// happened.
//
// The entry is held as a position in SpecifyManager::GetTimingChecks rather
// than as a pointer to it or a copy of it. A pointer would dangle, because
// SpecifyManager::AddTimingCheck appends to that vector during the run --
// §32.9's $sdf_annotate registers what an SDF file names -- and an append moves
// every element. A copy would freeze the limit, and §32.4.2's TIMINGCHECK
// annotation exists to change it; reading the entry back at every timecheck
// event is what lets an annotation reach a check already armed.
struct StabilityWindow {
  ArmedCheck armed;
  StabilityWindowEvents events;
  bool has_timestamp = false;
  uint64_t timestamp_ticks = 0;
};

// Reports the violation a check just detected, naming the signal that
// transitioned inside the window and the signal whose edge bounds it. §31.3.1
// and §31.3.2 both call the measured transition the data event and the bounding
// one the reference event, and they put them at opposite ends of the window,
// which is why the two messages differ in more than the name of the check.
//
// The report stands at SourceLoc::None(): §31.2's violation is a state the run
// reached rather than a construct that is illegal, and TimingCheckEntry records
// no source position for the declaration it was built from. Both signals are
// named under the instance prefix the check was registered with, so a reader
// can tell two instances of one cell apart.
void ReportViolation(TimingCheckKind kind, const StabilityWindow& window,
                     SimContext& ctx) {
  if (kind == TimingCheckKind::kSetup) {
    ReportTimingViolation(
        std::format("$setup violation: data signal {} transitioned inside the "
                    "window ending at reference signal {}",
                    window.events.timestamp_signal,
                    window.events.timecheck_signal),
        "31.3.1", ctx);
    return;
  }
  ReportTimingViolation(
      std::format("$hold violation: data signal {} transitioned inside the "
                  "window beginning at reference signal {}",
                  window.events.timecheck_signal,
                  window.events.timestamp_signal),
      "31.3.2", ctx);
}

// The timecheck event of a §31.3 check has arrived at `timecheck_ticks`.
// Reports a violation when the timestamp event fell inside the window the two
// clauses define, and does nothing until a timestamp event has been seen at
// all: §31.3 defines the window with respect to one transition, and before the
// first there is no window to place anything in.
void EvaluateStabilityWindow(const StabilityWindow& window,
                             uint64_t timecheck_ticks, SimContext& ctx) {
  if (!window.has_timestamp) return;
  const TimingCheckEntry& check = window.armed.Entry();
  bool violated = check.kind == TimingCheckKind::kSetup
                      ? SetupWindowViolated(check.limit, window.timestamp_ticks,
                                            timecheck_ticks)
                      : HoldWindowViolated(check.limit, window.timestamp_ticks,
                                           timecheck_ticks);
  if (!violated) return;
  ReportViolation(check.kind, window, ctx);
  ToggleNotifier(check, ctx);
}

// Arms the two watchers one §31.3 check needs. Nothing is armed when either
// signal names no variable of the design, which is what a check whose specify
// block was registered for a module the design never elaborated leaves behind.
void ArmStabilityWindow(const SpecifyManager& mgr, std::size_t index,
                        SimContext& ctx) {
  StabilityWindowEvents events = EventsOf(mgr.GetTimingChecks()[index]);
  Variable* timestamp_var = ctx.FindVariable(events.timestamp_signal);
  Variable* timecheck_var = ctx.FindVariable(events.timecheck_signal);
  if (timestamp_var == nullptr || timecheck_var == nullptr) return;
  SpecifyEdge timestamp_edge = events.timestamp_edge;
  SpecifyEdge timecheck_edge = events.timecheck_edge;
  auto window = std::make_shared<StabilityWindow>();
  window->armed = ArmedCheck{&mgr, index};
  window->events = std::move(events);
  WatchEdge(timestamp_var, timestamp_edge, [window, &ctx]() {
    window->has_timestamp = true;
    window->timestamp_ticks = ctx.CurrentTime().ticks;
  });
  WatchEdge(timecheck_var, timecheck_edge, [window, &ctx]() {
    EvaluateStabilityWindow(*window, ctx.CurrentTime().ticks, ctx);
  });
}

}  // namespace

void WatchTimingChecks(const SpecifyManager& mgr, SimContext& ctx) {
  const std::vector<TimingCheckEntry>& checks = mgr.GetTimingChecks();
  for (std::size_t i = 0; i < checks.size(); ++i) {
    switch (checks[i].kind) {
      case TimingCheckKind::kSetup:
      case TimingCheckKind::kHold:
        ArmStabilityWindow(mgr, i, ctx);
        break;
      case TimingCheckKind::kSetuphold:
      case TimingCheckKind::kRecovery:
      case TimingCheckKind::kRemoval:
      case TimingCheckKind::kRecrem:
        ArmStabilityPair(mgr, i, ctx);
        break;
      case TimingCheckKind::kWidth:
      case TimingCheckKind::kPeriod:
      case TimingCheckKind::kNochange:
        ArmPulseWindow(mgr, i, ctx);
        break;
      case TimingCheckKind::kSkew:
      case TimingCheckKind::kTimeskew:
      case TimingCheckKind::kFullskew:
        ArmSkewWindow(mgr, i, ctx);
        break;
    }
  }
}

}  // namespace delta
