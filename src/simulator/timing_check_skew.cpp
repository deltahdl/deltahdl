// §31.4.1's $skew, §31.4.2's $timeskew and §31.4.3's $fullskew, evaluated
// against a running design. ArmSkewWindow, declared in
// simulator/timing_check_skew.h, is what
// WatchTimingChecks (simulator/timing_check_driver.cpp) hands each of those
// three kinds to; it arms one watcher on each of the check's two signals and
// keeps, between them, the timing window §31.4 measures.
//
// These three do not fit the shape simulator/timing_check_driver.cpp evaluates
// §31.3.1's $setup and §31.3.2's $hold in. A stability window places one
// signal's transition inside a window the other bounds, so the two events are
// fixed: the reference event of a $setup always closes the window and the data
// event of a $hold always does. §31.4 measures how far apart two signals move
// instead. §31.4.3 goes further and settles the two roles at run time: "The
// reference event is the timestamp event, and the data event is the timecheck
// event when the reference event precedes the data event. The data event is the
// timestamp event, and the reference event is the timecheck event when the data
// event precedes the reference event." Which limit applies follows from that --
// §31.4.3 sets "limit to limit1 when the reference event transitions first and
// set to limit2 when the data event transitions first" -- so a $fullskew window
// carries the role its opening transition assigned.
//
// §31.4 also splits the three by *when* a violation is detected: "The skew
// checks have two different violation detection mechanisms, event-based and
// timer-based. Event-based skew checking is performed only when a signal
// transitions, while timer-based skew checking takes place as soon as the
// simulation time equal to the skew limit has elapsed." §31.4.1 makes $skew
// event-based outright. §31.4.2 and §31.4.3 are timer-based by default and are
// switched to event-based by an event_based_flag argument. TimingCheckEntry
// (simulator/specify_timing_check.h) carries a field for neither
// event_based_flag nor remain_active_flag, so a check reaching here is a check
// written without them, and this file implements the default of each clause:
// event-based for §31.4.1, timer-based for §31.4.2 and §31.4.3. The event-based
// mode of the latter two is unreachable until the entry carries the flag, and
// so is every rule §31.4.2 and §31.4.3 key to remain_active_flag, each of which
// governs a reference event whose `&&&` condition is false. ArmSkewWindow does
// read TimingCheckEntry::ref_condition_expr and
// TimingCheckEntry::data_condition_expr, through ArmTimingCheckEvents
// (simulator/timing_check_driver_internal.h), so the MODE conditions of Figure
// 31-1, Figure 31-2 and Figure 31-3 reach the run; the comment above that call
// states which half of each of them is reproduced.
//
// The timer is a scheduled event, which is what makes the timer-based mode a
// mechanism rather than a predicate: ArmTimeout below schedules the report at
// the moment the limit expires and cancels it if the timecheck event arrives
// first. It is scheduled into Region::kPrePostponed because §31.4.2 and §31.4.3
// both rule that the check "shall also not report a violation if a new
// timestamp event occurs exactly at the expiration of the time limit", and
// §31.4.3 rules the same for a timecheck event "within the time limit".
// Scheduler::ExecuteTimeSlot (simulator/scheduler.cpp) reaches kPrePostponed
// only once the active and reactive region sets of the slot are drained, so
// every transition committed at the expiration time has already been seen when
// the timeout runs, and a limit of zero therefore reports nothing when both
// signals move together -- which §31.4.1, §31.4.2 and §31.4.3 each require in
// the same words.
//
// simulator/specify_timing_check.h already models these three temporal rules:
// SkewChecker for §31.4.1, TimeskewChecker for §31.4.2, and
// ReportsTimeskewViolation, ReportsFullskewViolation and
// FullskewSecondTimestampAction (simulator/specify_timing_violation.cpp) for
// the per-event verdicts of §31.4.2 and §31.4.3. None is instantiated here,
// because each takes its limit as a constructor or call argument and a watcher
// must not hold one: §32.4.2's TIMINGCHECK annotation exists to change a
// registered check's limit during the run, which is why ArmedCheck
// (simulator/timing_check_driver_internal.h) holds a position in
// SpecifyManager::GetTimingChecks and this file reads the entry back at every
// event. The one value that is frozen is the limit a timer was scheduled
// against, since the deadline was computed from it and reporting any other
// number would describe a window that was never measured.
//
// Nothing calls SpecifyManager::CheckSkewViolation,
// SpecifyManager::CheckTimeskewViolation or
// SpecifyManager::CheckFullskewViolation, for the reason the comment at the top
// of simulator/timing_check_driver.cpp gives: those select a check by the
// spelling of its signals with no comparison of TimingCheckEntry::inst_prefix,
// so with one check registered per module instance a single call answers for
// every instance of the cell. A watcher already knows which entry it was armed
// for.

#include "simulator/timing_check_skew.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <memory>
#include <string>
#include <utility>

#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/timing_check_driver_internal.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// One §31.4 check between the two transitions it measures: which entry it is,
// the two signals it watches under the instance prefix the check was registered
// with, and the timing window that is open, if one is.
//
// `ref_is_timestamp` is what §31.4.3 decides at run time and what §31.4.1's
// Table 31-7 and §31.4.2's Table 31-8 fix in advance, both naming the
// reference_event the timestamp event and the data_event the timecheck event.
// It selects the limit of the open window, so a $fullskew window opened by the
// data signal is measured against limit2.
//
// `timeout_cancelled` is the guard the pending timer-based report was tagged
// with. Setting it through CancelTimeout both stops the callback doing work and
// lets Scheduler::Run drop the orphaned event without advancing simulation time
// to it, so a cancelled timeout cannot hold a run open past its last real
// activity.
struct SkewWindow {
  ArmedCheck armed;
  std::string ref_signal;
  std::string data_signal;
  bool open = false;
  bool ref_is_timestamp = true;
  uint64_t timestamp_ticks = 0;
  std::shared_ptr<bool> timeout_cancelled;
};

// §31.4.3: "The first limit is the maximum time by which the data event should
// follow the reference event. The second limit is the maximum time by which the
// reference event should follow the data event." §31.4.1 and §31.4.2 write one
// limit and always make the reference event the timestamp event, so the first
// is the only one their windows reach.
uint64_t WindowLimit(const TimingCheckEntry& check, bool ref_is_timestamp) {
  return ref_is_timestamp ? check.limit : check.limit2;
}

// Reports the violation the window just produced and updates §31.6's notifier.
// `limit` is the limit the window was measured against, which for a $fullskew
// is limit1 or limit2 according to which signal opened it.
//
// §31.9.4 gives an invocation option that switches every timing check off, and
// SpecifyManager::CheckSetupholdViolation
// (simulator/specify_timing_violation.cpp) reads it before answering. A check
// that is switched off reports nothing and toggles no notifier, so the option
// is read here, at the one point every violation of the three kinds passes
// through, rather than where a window is armed: the option can be selected
// during the run through SpecifyManager::SetTimingCheckInvocationOptions, and a
// window armed before that must still fall silent.
void ReportSkewViolation(const SkewWindow& window, uint64_t limit,
                         SimContext& ctx) {
  const TimingCheckEntry& check = window.armed.Entry();
  if (window.armed.mgr->GetTimingCheckInvocationOptions()
          .all_timing_checks_off) {
    return;
  }
  if (check.kind == TimingCheckKind::kFullskew) {
    ReportTimingViolation(
        std::format("$fullskew violation: signals {} and {} moved more than "
                    "the {} time units the check allows apart",
                    window.ref_signal, window.data_signal, limit),
        "31.4.3", ctx);
  } else if (check.kind == TimingCheckKind::kSkew) {
    ReportTimingViolation(
        std::format("$skew violation: data signal {} followed reference signal "
                    "{} by more than the {} time units the check allows",
                    window.data_signal, window.ref_signal, limit),
        "31.4.1", ctx);
  } else {
    // $timeskew's message states what the timer detects rather than what
    // $skew's states. The timer fires at reference+limit, when the data signal
    // has not moved and -- for a reference that no data event ever follows --
    // never will, so a message saying the data signal "followed" the reference
    // by too much would name an event that has not happened. §31.4.1's $skew is
    // evaluated only after a data event, so "followed" is true there by
    // construction, and §31.4.3's wording claims nothing about which signal
    // moved second.
    ReportTimingViolation(
        std::format("$timeskew violation: data signal {} did not follow "
                    "reference signal {} within the {} time units the check "
                    "allows",
                    window.data_signal, window.ref_signal, limit),
        "31.4.2", ctx);
  }
  ToggleNotifier(check, ctx);
}

// Stops the pending timer-based report, if there is one. A window with no timer
// armed -- every $skew window, and any window already closed -- is left alone.
void CancelTimeout(SkewWindow& window) {
  if (window.timeout_cancelled != nullptr) *window.timeout_cancelled = true;
  window.timeout_cancelled = nullptr;
}

// Turns the check dormant: §31.4.2's "the check shall become dormant and report
// no more violations (even in response to data events) until after the next
// reference event", and §31.4.3's identical rule for a timecheck event arriving
// within the limit.
void CloseWindow(SkewWindow& window) {
  window.open = false;
  CancelTimeout(window);
}

// Schedules the timer-based report of §31.4.2 and §31.4.3: "A violation shall
// be reported immediately upon an elapse of time after the reference event
// equal to the limit", after which the check is dormant. Only the open window
// is reported on, so a timeout that outlives its window does nothing; the guard
// is checked as well because Scheduler::DrainQueue runs a superseded event's
// callback and reads the flag only to decide whether the event was worth
// advancing time for.
void ArmTimeout(const std::shared_ptr<SkewWindow>& window, SimContext& ctx) {
  const uint64_t kLimit =
      WindowLimit(window->armed.Entry(), window->ref_is_timestamp);
  auto cancelled = std::make_shared<bool>(false);
  window->timeout_cancelled = cancelled;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->superseded = cancelled;
  event->callback = [window, cancelled, kLimit, &ctx]() {
    if (*cancelled || !window->open) return;
    CloseWindow(*window);
    ReportSkewViolation(*window, kLimit, ctx);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime() + SimTime{kLimit},
                                   Region::kPrePostponed, event);
}

// A timestamp event has arrived, on the reference signal when `ref_moved` is
// set and on the data signal otherwise. §31.4.1: "A second consecutive
// reference event shall cancel the old wait for the data event and begin a new
// one", and §31.4.3 says the same of a second timestamp event, which "starts a
// new timing window that replaces the first one". §31.4.3 adds that a timestamp
// event reaching a dormant check activates it, which is what setting `open`
// unconditionally does.
//
// A timer is armed for every kind but $skew, §31.4.1 making that one
// event-based: it "is evaluated only after a data event", and "if there is
// never a data event ... no timing violation shall ever be reported".
void OnTimestampEvent(const std::shared_ptr<SkewWindow>& window, bool ref_moved,
                      SimContext& ctx) {
  CancelTimeout(*window);
  window->open = true;
  window->ref_is_timestamp = ref_moved;
  window->timestamp_ticks = ctx.CurrentTime().ticks;
  if (window->armed.Entry().kind == TimingCheckKind::kSkew) return;
  ArmTimeout(window, ctx);
}

// §31.4.1: the data event is $skew's timecheck event, and the check "reports a
// violation in the following case: (timecheck time) - (timestamp time) >
// limit". The subtraction is guarded by the clause's own rule that
// "simultaneous transitions on the reference and data signals shall not cause
// $skew to report a timing violation, even when the skew limit value is zero",
// so a data event at or before the timestamp is no violation whatever the
// limit.
//
// The window stays open: §31.4.1 rules that "after a reference event, the $skew
// timing check shall never stop checking data events for a timing violation"
// and "shall report timing violations for all data events occurring beyond the
// limit after a reference event".
void OnSkewDataEvent(SkewWindow& window, SimContext& ctx) {
  if (!window.open) return;
  const uint64_t kNow = ctx.CurrentTime().ticks;
  if (kNow <= window.timestamp_ticks) return;
  const TimingCheckEntry& check = window.armed.Entry();
  if (kNow - window.timestamp_ticks <= check.limit) return;
  ReportSkewViolation(window, check.limit, ctx);
}

// §31.4.2, timer-based: "if a data event occurs within the limit, then a
// violation shall not be reported, and the check shall become dormant
// immediately". A data event that reaches an open window is necessarily within
// the limit, because the timeout at reference+limit would have closed the
// window otherwise, so there is nothing to compare and nothing to report.
void OnTimeskewDataEvent(SkewWindow& window) { CloseWindow(window); }

// §31.4.3: "A reference event or data event is a timestamp event and starts a
// new timing window, unless it is a timecheck event occurring within the time
// limit after a preceding timestamp event, in which case it turns the timing
// check dormant." The timecheck event is the transition of whichever signal did
// not open the window, and reaching an open window is what makes it fall within
// the limit.
void OnFullskewEvent(const std::shared_ptr<SkewWindow>& window, bool ref_moved,
                     SimContext& ctx) {
  if (window->open && window->ref_is_timestamp != ref_moved) {
    CloseWindow(*window);
    return;
  }
  OnTimestampEvent(window, ref_moved, ctx);
}

// The reference signal made the transition the check was written with. It is a
// timestamp event for $skew and $timeskew, whose tables fix the roles, and
// either role for $fullskew, whose Table 31-9 calls each argument a "timestamp
// or timecheck event".
void OnRefEdge(const std::shared_ptr<SkewWindow>& window, SimContext& ctx) {
  if (window->armed.Entry().kind == TimingCheckKind::kFullskew) {
    OnFullskewEvent(window, true, ctx);
    return;
  }
  OnTimestampEvent(window, true, ctx);
}

// The data signal made the transition the check was written with. It is the
// timecheck event of a $skew and of a $timeskew, and the two clauses answer it
// differently because §31.4.1 detects the violation on this event and §31.4.2
// has already detected it on its timer.
void OnDataEdge(const std::shared_ptr<SkewWindow>& window, SimContext& ctx) {
  const TimingCheckKind kKind = window->armed.Entry().kind;
  if (kKind == TimingCheckKind::kFullskew) {
    OnFullskewEvent(window, false, ctx);
    return;
  }
  if (kKind == TimingCheckKind::kSkew) {
    OnSkewDataEvent(*window, ctx);
    return;
  }
  OnTimeskewDataEvent(*window);
}

}  // namespace

void ArmSkewWindow(const SpecifyManager& mgr, std::size_t index,
                   SimContext& ctx) {
  auto window = std::make_shared<SkewWindow>();
  window->armed = ArmedCheck{&mgr, index};
  // ArmTimingCheckEvents (simulator/timing_check_driver_internal.h) arms one
  // watcher on the reference_event and one on the data_event, each gated by
  // §31.5's edge_control_specifier and §31.7's `&&&` condition its own event
  // was written with. A transition whose condition does not hold is not an
  // occurrence of the check at all, and it therefore opens no window and closes
  // none.
  //
  // Suppressing the event outright is only half of what §31.4.2 and §31.4.3
  // give a conditioned *reference* event whose condition is false. Both clauses
  // have such an event turn the check dormant unless the check's
  // remain_active_flag is set, in which case the event is discarded and any
  // open window stands. Discarding it is what happens here, so what this file
  // implements is the remain_active_flag-set behaviour, applied to every check.
  // TimingCheckEntry (simulator/specify_timing_check.h) carries a field for
  // neither event_based_flag nor remain_active_flag, although TimingCheckDecl
  // (parser/ast_specify.h) parses both into TimingCheckDecl::event_based_flag
  // and TimingCheckDecl::remain_active_flag, so the two behaviours cannot be
  // told apart in this file today; issue #3420 tracks carrying the flags
  // through to the entry. TimeskewChecker and FullskewSecondTimestampAction
  // (simulator/specify_timing_check.h) already state the dormant-versus-discard
  // rule, and are exercised only by unit tests.
  ArmedTimingCheckEvents events = ArmTimingCheckEvents(
      window->armed, ctx, [window, &ctx]() { OnRefEdge(window, ctx); },
      [window, &ctx]() { OnDataEdge(window, ctx); });
  window->ref_signal = std::move(events.ref_signal);
  window->data_signal = std::move(events.data_signal);
}

}  // namespace delta
