// §31.3's $setup and $hold, evaluated against a running design.
// WatchTimingChecks, declared in simulator/timing_check_driver.h, arms the
// watchers that do it. Everything else here answers one of the three questions
// evaluating a stability window asks: which transition of which signal closes
// the window (§31.3.1's Table 31-1 and §31.3.2's Table 31-2), whether a change
// of value is the edge the check was written with (§31.5), and what a violation
// does once found (§31.2's report and §31.6's notifier).
//
// SetupWindowViolated and HoldWindowViolated below restate the arithmetic of
// SpecifyManager::CheckSetupViolation and SpecifyManager::CheckHoldViolation
// (src/simulator/specify_timing_violation.cpp) from the two clauses those
// members read, rather than calling them. Both members select a check by the
// spelling of its signals -- `check.ref_signal != ref`, with no comparison of
// TimingCheckEntry::inst_prefix -- so with one check registered per module
// instance a single call answers for every instance of the cell, and answers
// true when any of them is violated. A watcher already knows which entry it was
// armed for, so it evaluates that entry and no other.

#include "simulator/timing_check_driver.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// The values §31.5's edge_descriptors are written over -- 0, 1 and the x that
// "edge transitions involving z are treated the same way as" -- plus the answer
// for a value that states no bit at all.
enum class EdgeLevel : uint8_t {
  kAbsent,
  kZero,
  kOne,
  kUnknown,
};

// The level of a signal's least significant bit. §31.5 writes an edge over one
// bit, so a vector signal is read at bit 0; §31.8's per-bit expansion of a
// vector signal into an independent check for each bit is a separate rule and
// is not applied here. A Logic4Vec with no words states no bit, which kAbsent
// is the answer for. x is (aval 1, bval 1) and z is (aval 0, bval 1), and §31.5
// reads the two alike, so the bval bit alone decides kUnknown.
EdgeLevel LevelOfLsb(const Logic4Vec& v) {
  if (v.nwords == 0) return EdgeLevel::kAbsent;
  if ((v.words[0].bval & 1U) != 0U) return EdgeLevel::kUnknown;
  return (v.words[0].aval & 1U) != 0U ? EdgeLevel::kOne : EdgeLevel::kZero;
}

// Whether a change from `from` to `to` is the edge `edge` names. §31.5 makes
// posedge the shorthand for edge[01, 0x, x1] and negedge the shorthand for
// edge[10, x0, 1x], so posedge is every transition that leaves 0 or arrives at
// 1, and negedge every transition that leaves 1 or arrives at 0. A value that
// did not change is no transition at all and is neither.
//
// SpecifyEdge::kNone is a timing_check_event written without an
// edge_control_specifier, which Syntax 31-2 (§31.2) allows and which no edge
// restricts, so every transition matches it. SpecifyEdge::kEdge is answered the
// same way and that answer is not exact: the edge_descriptor list an
// edge-control specifier was written with is parsed into
// TimingCheckDecl::ref_edge_descriptors (src/parser/ast_specify.h) and
// TimingCheckEntry (src/simulator/specify_timing_check.h) carries no field for
// it, so `edge[01]` cannot be told apart from `edge[10]` here.
bool TimingCheckEdgeMatches(SpecifyEdge edge, EdgeLevel from, EdgeLevel to) {
  if (from == EdgeLevel::kAbsent || to == EdgeLevel::kAbsent) return false;
  if (from == to) return false;
  if (edge == SpecifyEdge::kPosedge) {
    return from == EdgeLevel::kZero || to == EdgeLevel::kOne;
  }
  if (edge == SpecifyEdge::kNegedge) {
    return from == EdgeLevel::kOne || to == EdgeLevel::kZero;
  }
  return true;
}

// Arms on `var` a watcher that calls `on_edge` every time the variable's least
// significant bit makes the transition `edge` names, for as long as the run
// lasts.
//
// The watcher keeps the level it last saw rather than trusting that a
// notification means a change, for the reason WatchSourceVariable in
// src/simulator/module_path_delay.cpp keeps its own copy of the value:
// Variable::NotifyWatchers fires whenever a driver commits, and a driver may
// commit the value already there -- Net::Resolve in src/simulator/net.cpp
// notifies after every resolution. Comparing the level before the commit
// against the level after is what keeps such a commit from being read as an
// edge and reporting a violation no signal caused.
//
// It returns false so that NotifyWatchers re-arms it: a signal a timing check
// names transitions any number of times before the run ends.
void WatchEdge(Variable* var, SpecifyEdge edge, std::function<void()> on_edge) {
  auto seen = std::make_shared<EdgeLevel>(LevelOfLsb(var->value));
  var->AddWatcher([var, edge, seen, on_edge = std::move(on_edge)]() {
    EdgeLevel before = *seen;
    *seen = LevelOfLsb(var->value);
    if (TimingCheckEdgeMatches(edge, before, *seen)) on_edge();
    return false;
  });
}

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
  const SpecifyManager* mgr = nullptr;
  std::size_t index = 0;
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
    ctx.GetDiag().Warning(
        SourceLoc::None(),
        std::format("$setup violation: data signal {} transitioned inside the "
                    "window ending at reference signal {}",
                    window.events.timestamp_signal,
                    window.events.timecheck_signal),
        Subclause("31.3.1"));
    return;
  }
  ctx.GetDiag().Warning(
      SourceLoc::None(),
      std::format("$hold violation: data signal {} transitioned inside the "
                  "window beginning at reference signal {}",
                  window.events.timecheck_signal,
                  window.events.timestamp_signal),
      Subclause("31.3.2"));
}

// §31.6: "Whenever a timing violation occurs, the timing check updates the
// value of the notifier", and Table 31-13 gives the value it updates to.
// ToggleNotifierOnViolation (src/simulator/specify_timing_check.h) is that
// table. §31.6 has the notifier "declared in the module where timing check
// tasks are invoked", which is the module whose specify block declared the
// check, so it is looked up under the same instance prefix the check's two
// signals are.
//
// Only the least significant bit is written and the rest of the variable is
// left as it stands, Table 31-13 stating one value and §31.6's notifier being a
// scalar. The write goes through Variable::NotifyWatchers because §31.6 has a
// model "use the notifier to make behavior a function of timing check
// violations", and an `always @(notifier)` sees the new value only once the
// watchers have been notified.
void ToggleNotifier(const TimingCheckEntry& check, SimContext& ctx) {
  if (check.notifier.empty()) return;
  Variable* var = ctx.FindVariable(check.inst_prefix + check.notifier);
  if (var == nullptr || var->value.nwords == 0) return;
  Logic4Word toggled = ToggleNotifierOnViolation(var->value.words[0]);
  var->value.words[0].aval =
      (var->value.words[0].aval & ~1ULL) | (toggled.aval & 1ULL);
  var->value.words[0].bval =
      (var->value.words[0].bval & ~1ULL) | (toggled.bval & 1ULL);
  var->NotifyWatchers();
}

// The timecheck event of a §31.3 check has arrived at `timecheck_ticks`.
// Reports a violation when the timestamp event fell inside the window the two
// clauses define, and does nothing until a timestamp event has been seen at
// all: §31.3 defines the window with respect to one transition, and before the
// first there is no window to place anything in.
void EvaluateStabilityWindow(const StabilityWindow& window,
                             uint64_t timecheck_ticks, SimContext& ctx) {
  if (!window.has_timestamp) return;
  const TimingCheckEntry& check = window.mgr->GetTimingChecks()[window.index];
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
  window->mgr = &mgr;
  window->index = index;
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
    TimingCheckKind kind = checks[i].kind;
    // §31.3's other four stability-window checks, §31.4's clock and control
    // signal checks and §31.9's negative timing checks name their two
    // transitions differently, and none of them is armed here.
    if (kind != TimingCheckKind::kSetup && kind != TimingCheckKind::kHold) {
      continue;
    }
    ArmStabilityWindow(mgr, i, ctx);
  }
}

}  // namespace delta
