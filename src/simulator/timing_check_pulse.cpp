// §31.4.4's $width, §31.4.5's $period and §31.4.6's $nochange, evaluated
// against a running design. ArmPulseWindow, declared in
// simulator/timing_check_pulse.h, is handed an entry of one of those three
// kinds by WatchTimingChecks (src/simulator/timing_check_driver.cpp); it finds
// the variables the entry names and arms the watchers that measure the check.
//
// The three belong together because the reference signal bounds the window at
// both ends. §31.4.4 derives the data event as "reference event signal with
// opposite edge" and §31.4.5 as "reference event signal with the same edge", so
// each names one signal and measures between two edges of it, and the state a
// watcher carries is the time of the previous matching edge. §31.4.6 names a
// data signal as well, and takes the leading edge of the reference event for
// the beginning of its window and the trailing edge for the end, so a watcher
// there carries both reference times and reports a data transition that fell
// between them.
//
// The three predicates below -- WidthPulseViolated, PeriodViolated and
// NochangeWindowViolated -- restate the arithmetic of
// SpecifyManager::CheckWidthViolation, SpecifyManager::CheckPeriodViolation and
// SpecifyManager::CheckNochangeViolation
// (src/simulator/specify_timing_violation.cpp) from the clauses those members
// read, rather than calling them. Each of those members selects a check by the
// spelling of its signals -- `check.ref_signal != ref`, with no comparison of
// TimingCheckEntry::inst_prefix -- so with one check registered per module
// instance a single call answers for every instance of the cell, and answers
// true when any of them is violated. A watcher already knows which entry it was
// armed for, so it evaluates that entry and no other.

#include "simulator/timing_check_pulse.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "parser/ast_specify.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/timing_check_driver_internal.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// §31.9.4: the invocation option that switches every timing check off, read
// through SpecifyManager::GetTimingCheckInvocationOptions. It is read at each
// event rather than when the watcher is armed, because
// SpecifyManager::SetTimingCheckInvocationOptions can be called after
// WatchTimingChecks has run and the option then has to reach a check already
// armed. SpecifyManager::CheckSetupholdViolation reads the same option to
// return false, which is the behavior restated here.
bool AllTimingChecksOff(const ArmedCheck& armed) {
  return armed.mgr->GetTimingCheckInvocationOptions().all_timing_checks_off;
}

// The edge §31.4.4 derives its data event with: "data event = reference event
// signal with opposite edge". posedge and negedge are each other's opposite.
//
// SpecifyEdge::kEdge is returned unchanged, and that answer is not exact. An
// edge-control specifier is an edge specification, so §31.4.4's "A compilation
// error shall occur if the reference event is not an edge specification" does
// not rule one out, and ValidateTimingCheckEdgeRequired
// (src/parser/parser_specify.cpp) rejects only SpecifyEdge::kNone. The
// edge_descriptor list is parsed into TimingCheckDecl::ref_edge_descriptors and
// TimingCheckEntry carries no field for it, so `edge[01]` cannot be told from
// `edge[10]` here and its opposite cannot be named. Both watchers then match
// every transition, and the check measures between consecutive transitions of
// any direction.
SpecifyEdge OppositeEdge(SpecifyEdge edge) {
  if (edge == SpecifyEdge::kPosedge) return SpecifyEdge::kNegedge;
  if (edge == SpecifyEdge::kNegedge) return SpecifyEdge::kPosedge;
  return edge;
}

// §31.4.4: "threshold < (timecheck time) - (timestamp time) < limit". Both end
// points are excluded, so a pulse exactly as wide as the limit satisfies the
// check -- the clause has the width "greater than or equal to limit in order to
// avoid a timing violation" -- and a pulse no wider than the threshold is
// passed over, the clause stating that "no violation is reported for glitches
// smaller than the threshold". A check declared without the optional threshold
// argument carries the zero §31.4.4 makes its default, which excludes nothing
// but a pulse of no width at all.
bool WidthPulseViolated(const TimingCheckEntry& check, uint64_t elapsed) {
  return elapsed > check.threshold && elapsed < check.limit;
}

// §31.4.5: "(timecheck time) - (timestamp time) < limit", the two times being
// consecutive edges of one signal in the same direction, since §31.4.5 derives
// the data event as "reference event signal with the same edge". A zero limit
// therefore issues no violation, no elapsed time being below it.
bool PeriodViolated(const TimingCheckEntry& check, uint64_t elapsed) {
  return elapsed < check.limit;
}

// One §31.4.4 or §31.4.5 check between the two edges of its signal it measures:
// which entry it is, the signal under the instance prefix the check was
// registered with, and when the edge that opens the window last arrived.
//
// The entry is held as a position in SpecifyManager::GetTimingChecks rather
// than as a pointer to it or a copy of it, which is what ArmedCheck
// (src/simulator/timing_check_driver_internal.h) is for: an entry's limit can
// change during the run and the vector holding it can move.
struct PulseWindow {
  ArmedCheck armed;
  std::string signal;
  bool has_timestamp = false;
  uint64_t timestamp_ticks = 0;
};

// Reports the violation a $width or a $period check just measured, naming the
// one signal it watches and the two numbers §31.4.4 and §31.4.5 compare: the
// time that elapsed between the two edges, and the limit the check requires it
// to reach. The signal is named under the instance prefix the check was
// registered with, so a reader can tell two instances of one cell apart.
void ReportPulseViolation(const TimingCheckEntry& check,
                          const std::string& signal, uint64_t elapsed,
                          SimContext& ctx) {
  if (check.kind == TimingCheckKind::kWidth) {
    ReportTimingViolation(
        std::format("$width violation: signal {} held its level for {} time "
                    "units, short of the {} the check requires",
                    signal, elapsed, check.limit),
        "31.4.4", ctx);
    return;
  }
  ReportTimingViolation(
      std::format("$period violation: signal {} repeated its edge after {} "
                  "time units, short of the {} the check requires",
                  signal, elapsed, check.limit),
      "31.4.5", ctx);
}

// The edge that closes a $width or a $period window has arrived at
// `timecheck_ticks`. Reports a violation when the time since the edge that
// opened the window falls short of what the check requires.
//
// Nothing is reported before an opening edge has been seen, there being no
// window to measure yet, and nothing is reported for a closing edge at or
// before the opening one. §31.4.4 states that the two "shall never occur at the
// same simulation time because these events are triggered by opposite
// transitions", and SpecifyManager::CheckWidthViolation and
// SpecifyManager::CheckPeriodViolation both skip a check whose data time is not
// past its reference time.
void EvaluatePulseWindow(const PulseWindow& window, uint64_t timecheck_ticks,
                         SimContext& ctx) {
  if (!window.has_timestamp) return;
  if (timecheck_ticks <= window.timestamp_ticks) return;
  if (AllTimingChecksOff(window.armed)) return;
  const TimingCheckEntry& check = window.armed.Entry();
  uint64_t elapsed = timecheck_ticks - window.timestamp_ticks;
  bool violated = check.kind == TimingCheckKind::kWidth
                      ? WidthPulseViolated(check, elapsed)
                      : PeriodViolated(check, elapsed);
  if (!violated) return;
  ReportPulseViolation(check, window.signal, elapsed, ctx);
  ToggleNotifier(check, ctx);
}

// Arms the two watchers a §31.4.4 check needs on the one signal it names: the
// reference edge opens the pulse and the opposite edge closes it.
//
// The closing watcher clears the opening time it measured against, so one
// opening edge is measured once. §31.5 makes a transition to x a negedge as
// readily as a transition to 0, so a signal going 1 to x to 0 offers two
// closing edges for one pulse, and without the clear the second would be
// measured against the same opening edge and reported again.
//
// The closing watcher is armed before the opening one, which decides nothing
// for the posedge and negedge a $width is written with -- no transition matches
// both -- and gives the SpecifyEdge::kEdge that OppositeEdge cannot invert the
// interval since the previous transition rather than an interval of zero.
void ArmWidthWindow(const SpecifyManager& mgr, std::size_t index,
                    SimContext& ctx) {
  const TimingCheckEntry& check = mgr.GetTimingChecks()[index];
  std::string signal = check.inst_prefix + check.ref_signal;
  Variable* var = ctx.FindVariable(signal);
  if (var == nullptr) return;
  SpecifyEdge opening_edge = check.ref_edge;
  auto window = std::make_shared<PulseWindow>();
  window->armed = ArmedCheck{&mgr, index};
  window->signal = std::move(signal);
  WatchEdge(var, OppositeEdge(opening_edge), [window, &ctx]() {
    EvaluatePulseWindow(*window, ctx.CurrentTime().ticks, ctx);
    window->has_timestamp = false;
  });
  WatchEdge(var, opening_edge, [window, &ctx]() {
    window->has_timestamp = true;
    window->timestamp_ticks = ctx.CurrentTime().ticks;
  });
}

// Arms the one watcher a §31.4.5 check needs. §31.4.5 derives the data event as
// the reference signal with the same edge, so every matching edge both closes
// the period that began at the previous one and opens the next; the opening
// time is replaced whether or not the period just measured was violated.
void ArmPeriodWindow(const SpecifyManager& mgr, std::size_t index,
                     SimContext& ctx) {
  const TimingCheckEntry& check = mgr.GetTimingChecks()[index];
  std::string signal = check.inst_prefix + check.ref_signal;
  Variable* var = ctx.FindVariable(signal);
  if (var == nullptr) return;
  SpecifyEdge edge = check.ref_edge;
  auto window = std::make_shared<PulseWindow>();
  window->armed = ArmedCheck{&mgr, index};
  window->signal = std::move(signal);
  WatchEdge(var, edge, [window, &ctx]() {
    uint64_t now = ctx.CurrentTime().ticks;
    EvaluatePulseWindow(*window, now, ctx);
    window->has_timestamp = true;
    window->timestamp_ticks = now;
  });
}

// One §31.4.6 check: which entry it is, the two signals it names under the
// instance prefix the check was registered with, the two reference edges that
// bound the window, and the data transitions seen while the window was still
// open.
//
// §31.4.6 puts the end of the window at "(trailing reference edge time) +
// end_edge_offset", so a data transition inside an open window cannot be
// answered when it happens -- a negative end_edge_offset shortens the region
// and can leave the transition outside it. Such a transition is held in
// `pending` and answered at the trailing edge, which is the first moment both
// end points are known.
struct NochangeWindow {
  ArmedCheck armed;
  std::string ref_signal;
  std::string data_signal;
  bool has_leading = false;
  uint64_t leading_ticks = 0;
  bool has_trailing = false;
  uint64_t trailing_ticks = 0;
  std::vector<uint64_t> pending;
};

// §31.4.6: "(beginning of time window) = (leading reference edge time) -
// start_edge_offset", "(end of time window) = (trailing reference edge time) +
// end_edge_offset", and the violation case is "(beginning of time window) <
// (data event time) < (end of time window)". The end points are not included,
// which is what makes the clause's own example -- `$nochange(posedge clk, data,
// 0, 0)` -- report nothing when the posedge and the data transition happen at
// the same simulation time.
//
// Both offsets are signed and both are subtracted from or added to the edge
// they move: a positive start_edge_offset starts the region earlier and a
// positive end_edge_offset ends it later, each extending the region, and a
// negative one shrinks it from that end.
bool NochangeWindowViolated(const TimingCheckEntry& check,
                            uint64_t leading_ticks, uint64_t trailing_ticks,
                            uint64_t data_ticks) {
  int64_t begin = static_cast<int64_t>(leading_ticks) - check.start_edge_offset;
  int64_t end = static_cast<int64_t>(trailing_ticks) + check.end_edge_offset;
  auto data = static_cast<int64_t>(data_ticks);
  return begin < data && data < end;
}

// A data transition of a §31.4.6 check at `data_ticks`, both reference edges of
// the window being known. Reports the violation when the transition fell inside
// the window.
void EvaluateNochangeData(const NochangeWindow& window, uint64_t data_ticks,
                          SimContext& ctx) {
  if (AllTimingChecksOff(window.armed)) return;
  const TimingCheckEntry& check = window.armed.Entry();
  if (!NochangeWindowViolated(check, window.leading_ticks,
                              window.trailing_ticks, data_ticks)) {
    return;
  }
  ReportTimingViolation(
      std::format("$nochange violation: data signal {} transitioned inside "
                  "the window bounded by reference signal {}",
                  window.data_signal, window.ref_signal),
      "31.4.6", ctx);
  ToggleNotifier(check, ctx);
}

// The trailing reference edge of a §31.4.6 check has arrived at
// `trailing_ticks`, which closes the window and settles its end point. Every
// data transition held while the window was open is answered now.
void CloseNochangeWindow(NochangeWindow& window, uint64_t trailing_ticks,
                         SimContext& ctx) {
  if (!window.has_leading) return;
  window.has_trailing = true;
  window.trailing_ticks = trailing_ticks;
  // The held transitions are moved out before any is answered. §31.6 has a
  // violation write the notifier through Variable::NotifyWatchers, and a
  // watcher run from there reaches RecordNochangeData below, which appends to
  // the vector this loop would otherwise be walking.
  std::vector<uint64_t> held = std::move(window.pending);
  window.pending.clear();
  for (uint64_t data_ticks : held) {
    EvaluateNochangeData(window, data_ticks, ctx);
  }
}

// A data transition of a §31.4.6 check at `data_ticks`. It is held until the
// trailing reference edge settles the end of the window, and answered straight
// away once that edge has arrived: §31.4.6's end_edge_offset can extend the
// region past the trailing edge, so a transition after the window closed is
// still inside it while that extension lasts.
//
// Nothing is held or answered before a leading reference edge has been seen,
// there being no window to place a transition in.
void RecordNochangeData(NochangeWindow& window, uint64_t data_ticks,
                        SimContext& ctx) {
  if (!window.has_leading) return;
  if (!window.has_trailing) {
    window.pending.push_back(data_ticks);
    return;
  }
  EvaluateNochangeData(window, data_ticks, ctx);
}

// Arms the three watchers a §31.4.6 check needs. §31.4.6 says so outright:
// "Unlike other timing checks, $nochange involves three, rather than two,
// transitions" -- the leading reference edge, the trailing one, and the data
// transition measured against them.
//
// The leading edge is the one the check was written with, which §31.4.6
// restricts to posedge or negedge, and the trailing edge is its opposite. A
// leading edge starts a fresh window and discards any data transition held for
// the one before it, which never closed.
void ArmNochangeWindow(const SpecifyManager& mgr, std::size_t index,
                       SimContext& ctx) {
  const TimingCheckEntry& check = mgr.GetTimingChecks()[index];
  std::string ref_signal = check.inst_prefix + check.ref_signal;
  std::string data_signal = check.inst_prefix + check.data_signal;
  Variable* ref_var = ctx.FindVariable(ref_signal);
  Variable* data_var = ctx.FindVariable(data_signal);
  if (ref_var == nullptr || data_var == nullptr) return;
  SpecifyEdge leading_edge = check.ref_edge;
  SpecifyEdge data_edge = check.data_edge;
  auto window = std::make_shared<NochangeWindow>();
  window->armed = ArmedCheck{&mgr, index};
  window->ref_signal = std::move(ref_signal);
  window->data_signal = std::move(data_signal);
  WatchEdge(ref_var, leading_edge, [window, &ctx]() {
    window->has_leading = true;
    window->has_trailing = false;
    window->leading_ticks = ctx.CurrentTime().ticks;
    window->pending.clear();
  });
  WatchEdge(ref_var, OppositeEdge(leading_edge), [window, &ctx]() {
    CloseNochangeWindow(*window, ctx.CurrentTime().ticks, ctx);
  });
  WatchEdge(data_var, data_edge, [window, &ctx]() {
    RecordNochangeData(*window, ctx.CurrentTime().ticks, ctx);
  });
}

}  // namespace

void ArmPulseWindow(const SpecifyManager& mgr, std::size_t index,
                    SimContext& ctx) {
  TimingCheckKind kind = mgr.GetTimingChecks()[index].kind;
  if (kind == TimingCheckKind::kWidth) {
    ArmWidthWindow(mgr, index, ctx);
    return;
  }
  if (kind == TimingCheckKind::kPeriod) {
    ArmPeriodWindow(mgr, index, ctx);
    return;
  }
  if (kind == TimingCheckKind::kNochange) ArmNochangeWindow(mgr, index, ctx);
}

}  // namespace delta
