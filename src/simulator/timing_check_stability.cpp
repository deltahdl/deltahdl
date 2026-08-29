// §31.3.3's $setuphold, §31.3.4's $removal, §31.3.5's $recovery and §31.3.6's
// $recrem, evaluated against a running design. ArmStabilityPair, declared in
// simulator/timing_check_stability.h, is what WatchTimingChecks
// (src/simulator/timing_check_driver.cpp) hands an entry of one of those four
// kinds; simulator/timing_check_driver_internal.h holds what every Clause 31
// driver shares -- §31.5's edge matching, the watcher that arms on an edge,
// §31.2's report and §31.6's notifier.
//
// All four name a reference event and a data event, as §31.3.1's $setup and
// §31.3.2's $hold do, and differ from those two in where the reference edge
// stands. Table 31-4 makes $removal's reference_event the timecheck event and
// its data_event the timestamp event, so a $removal window ends at the
// reference edge. Table 31-5 makes $recovery's reference_event the timestamp
// event and its data_event the timecheck event, so a $recovery window begins at
// it. Table 31-3 and Table 31-6 give $setuphold and $recrem no fixed answer at
// all: "either the reference event or the data event can be the timecheck
// event. It shall depend upon which occurs first in the simulation". Each of
// those two therefore bounds a window on both sides of the reference edge and
// carries one limit for each side.
//
// §31.3.3 and §31.3.6 state the two-sided pair as an equivalence, and that is
// what decides which limit bounds which side. §31.3.3 makes "$setuphold(
// posedge clk, data, tSU, tHLD )" equivalent in functionality to "$setup( data,
// posedge clk, tSU )" with "$hold( posedge clk, data, tHLD )", so the setup
// limit -- TimingCheckEntry::limit, the declaration's first -- bounds the side
// before the reference edge and the hold limit TimingCheckEntry::limit2 the
// side after it. §31.3.6 makes "$recrem( posedge clear, posedge clk, tREC, tREM
// )" equivalent in functionality to "$removal( posedge clear, posedge clk, tREM
// )" with "$recovery( posedge clear, posedge clk, tREC )", so for $recrem the
// two are the other way round: the removal limit TimingCheckEntry::limit2
// bounds the side before the reference edge and the recovery limit
// TimingCheckEntry::limit the side after it. Table 31-6 says the same thing in
// the vocabulary Table 31-3 uses, giving $recrem's removal limit the sentence
// Table 31-3 gives $setuphold's setup limit and its recovery limit the sentence
// Table 31-3 gives the hold limit.
//
// The window arithmetic below restates §31.3.3 through §31.3.6 rather than
// calling SpecifyManager::CheckSetupholdViolation,
// SpecifyManager::CheckRemovalViolation,
// SpecifyManager::CheckRecoveryViolation or
// SpecifyManager::CheckRecremViolation, for the reason
// simulator/timing_check_driver_internal.h gives: each of those selects a check
// by the spelling of its signals, with no comparison of
// TimingCheckEntry::inst_prefix, so with one check registered per module
// instance a single call answers for every instance of the cell. A watcher
// already knows which entry it was armed for, so it evaluates that entry and no
// other.

#include "simulator/timing_check_stability.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <memory>
#include <string>
#include <utility>

#include "parser/ast_specify.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/timing_check_driver_internal.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// Which side of the reference edge a check found the data transition on, or
// that it found no violation. §31.3.3 and §31.3.6 bound a window on both sides
// of that edge and name each side after the limit bounding it, so the side is
// what tells a $setuphold setup violation from a $setuphold hold one.
enum class StabilitySide : uint8_t {
  kNone,
  kBefore,
  kAfter,
};

// Which of a check's two signals just made the transition it was written with.
// §31.3 evaluates a check at its timecheck event, and Table 31-4 and Table 31-5
// put that event on opposite signals, so which watcher fired is what decides
// whether there is anything to evaluate.
enum class StabilityEvent : uint8_t {
  kReference,
  kData,
};

// The two limits of a §31.3.3 or §31.3.6 check, each named for the side of the
// reference edge it bounds rather than for the constraint that declared it. The
// signed pair carries the same two limits as §31.9 wrote them, which is what a
// check with negative-value handling in force is evaluated against.
struct TwoSidedLimits {
  uint64_t before = 0;
  uint64_t after = 0;
  int64_t signed_before = 0;
  int64_t signed_after = 0;
};

// $setuphold's setup limit bounds the side before the reference edge and its
// hold limit the side after it; $recrem's removal limit bounds the side before
// and its recovery limit the side after. A declaration writes setup before hold
// and recovery before removal, so the two kinds fill TimingCheckEntry::limit
// and TimingCheckEntry::limit2 in opposite orders and only $recrem's have to be
// swapped here. §31.3.3's and §31.3.6's equivalences are what state the two
// orders, and they are the orders SpecifyManager::CheckSetupholdViolation and
// SpecifyManager::CheckRecremViolation select their limits in.
TwoSidedLimits LimitsOf(const TimingCheckEntry& check) {
  if (check.kind == TimingCheckKind::kRecrem) {
    return TwoSidedLimits{check.limit2, check.limit, check.signed_limit2,
                          check.signed_limit};
  }
  return TwoSidedLimits{check.limit, check.limit2, check.signed_limit,
                        check.signed_limit2};
}

// §31.3.3, with both limits positive and the data event occurring first:
// "(beginning of time window) = (timecheck time) - limit", "(end of time
// window) = (timecheck time)", and a violation is reported when "(beginning of
// time window) < (timestamp time) <= (end of time window)". With the data event
// occurring second: "(beginning of time window) = (timestamp time)", "(end of
// time window) = (timestamp time) + limit", and a violation is reported when
// "(beginning of time window) <= (timecheck time) < (end of time window)".
// §31.3.6 states both cases in the same words for $recrem.
//
// Either way the reference edge is the end point that is inside the violation
// region, which is what makes both clauses' "shall report a timing violation
// when the reference and data events occur simultaneously" hold. A simultaneous
// pair is read against the before-side limit, which is where
// SpecifyManager::CheckSetupholdViolation reads it. Both clauses state that a
// check whose two limits are zero shall never issue a violation.
bool TwoSidedWindowViolated(const TwoSidedLimits& limits, uint64_t ref_ticks,
                            uint64_t data_ticks) {
  if (limits.before == 0 && limits.after == 0) return false;
  if (data_ticks <= ref_ticks) return ref_ticks - data_ticks < limits.before;
  return data_ticks - ref_ticks < limits.after;
}

// §31.9.1 requirement (a): "A timing violation shall be triggered if the signal
// changes in the violation window, exclusive of the end points. Violation
// windows smaller than two units of simulation precision cannot yield timing
// violations." A negative limit moves an end point across the reference edge
// rather than bounding one side of it, so the window is the one open interval
// the two signed limits mark out around the reference time and neither side is
// answered on its own.
//
// Excluding both end points settles the second sentence as well. SimTime::ticks
// counts in units of SimContext::GlobalPrecision, so a window narrower than two
// of those units holds no tick strictly inside it and reports nothing whatever
// the data transition does.
bool NegativeWindowViolated(const TwoSidedLimits& limits, uint64_t ref_ticks,
                            uint64_t data_ticks) {
  const auto kRefTicks = static_cast<int64_t>(ref_ticks);
  const auto kDataTicks = static_cast<int64_t>(data_ticks);
  return kDataTicks > kRefTicks - limits.signed_before &&
         kDataTicks < kRefTicks + limits.signed_after;
}

// §31.3.4: "(beginning of time window) = (timecheck time) - limit", "(end of
// time window) = (timecheck time)", a violation is reported when "(beginning of
// time window) < (timestamp time) < (end of time window)", and "the end points
// of the time window are not part of the violation region". Table 31-4 makes
// the reference event the timecheck event and the data event the timestamp
// event, so the window ends at the reference edge and the data transition is
// what is placed inside it. When the limit is zero the check never issues a
// violation, which the excluded end points already give.
bool RemovalWindowViolated(uint64_t limit, uint64_t ref_ticks,
                           uint64_t data_ticks) {
  return data_ticks < ref_ticks && ref_ticks - data_ticks < limit;
}

// §31.3.5: "(beginning of time window) = (timestamp time)", "(end of time
// window) = (timestamp time) + limit", a violation is reported when "(beginning
// of time window) <= (timecheck time) < (end of time window)", and "only the
// end of the time window is not part of the violation region". Table 31-5 makes
// the reference event the timestamp event and the data event the timecheck
// event, so the window begins at the reference edge. When the limit is zero the
// check never issues a violation, which the excluded end is what gives.
bool RecoveryWindowViolated(uint64_t limit, uint64_t ref_ticks,
                            uint64_t data_ticks) {
  return data_ticks >= ref_ticks && data_ticks - ref_ticks < limit;
}

// Whether one of §31.3.3's and §31.3.6's two-sided checks is violated, and on
// which side of the reference edge.
//
// §31.9.4 has an invocation option that turns every timing check off, and these
// are the two kinds whose verdict reads it:
// SpecifyManager::CheckSetupholdViolation and
// SpecifyManager::CheckRecremViolation both return false while
// TimingCheckInvocationOptions::all_timing_checks_off is set, and
// SpecifyManager::GetTimingCheckInvocationOptions is how a watcher reaches that
// option. Whether §31.9's negative limits are honored at all is settled before
// an entry ever reaches here: BuildTimingCheckUnderOptions
// (src/simulator/specify_timing_check.cpp) sets
// TimingCheckEntry::negative_timing_check_enabled only while §31.9.4's enabling
// option is in force, and SpecifyManager::ApplyTimingCheckInvocationOptions
// clears it again when that option goes away.
StabilitySide TwoSidedSide(const SpecifyManager& mgr,
                           const TimingCheckEntry& check, uint64_t ref_ticks,
                           uint64_t data_ticks) {
  if (mgr.GetTimingCheckInvocationOptions().all_timing_checks_off) {
    return StabilitySide::kNone;
  }
  TwoSidedLimits limits = LimitsOf(check);
  bool violated = check.negative_timing_check_enabled
                      ? NegativeWindowViolated(limits, ref_ticks, data_ticks)
                      : TwoSidedWindowViolated(limits, ref_ticks, data_ticks);
  if (!violated) return StabilitySide::kNone;
  return data_ticks <= ref_ticks ? StabilitySide::kBefore
                                 : StabilitySide::kAfter;
}

// Whether the check `check` is violated by a data transition at `data_ticks`
// against a reference transition at `ref_ticks`, and on which side of the
// reference edge the data transition fell. §31.3.4 and §31.3.5 carry one limit
// and bound one side apiece, so the side a violation of either falls on is
// fixed by the clause rather than by the two times.
StabilitySide ViolatedSide(const SpecifyManager& mgr,
                           const TimingCheckEntry& check, uint64_t ref_ticks,
                           uint64_t data_ticks) {
  if (check.kind == TimingCheckKind::kSetuphold ||
      check.kind == TimingCheckKind::kRecrem) {
    return TwoSidedSide(mgr, check, ref_ticks, data_ticks);
  }
  if (check.kind == TimingCheckKind::kRemoval) {
    return RemovalWindowViolated(check.limit, ref_ticks, data_ticks)
               ? StabilitySide::kBefore
               : StabilitySide::kNone;
  }
  return RecoveryWindowViolated(check.limit, ref_ticks, data_ticks)
             ? StabilitySide::kAfter
             : StabilitySide::kNone;
}

// Whether the transition just seen is the check's timecheck event, which is the
// event §31.3 evaluates a check at. Table 31-4 makes $removal's reference event
// the timecheck event and Table 31-5 makes $recovery's data event the timecheck
// event; Table 31-3 and Table 31-6 leave $setuphold's and $recrem's to
// whichever of the two "occurs first in the simulation", so for those two
// either transition closes a window.
bool ClosesWindow(TimingCheckKind kind, StabilityEvent event) {
  if (kind == TimingCheckKind::kRemoval) {
    return event == StabilityEvent::kReference;
  }
  if (kind == TimingCheckKind::kRecovery) {
    return event == StabilityEvent::kData;
  }
  return true;
}

// One §31.3 check between the two transitions it measures: which entry it is,
// what its two signals are called, and when each of them last made the
// transition the check was written with. Both signals are named under the
// instance prefix the check was registered with, which is what every variable
// of an instantiated module is named under.
//
// The entry is held as a position in SpecifyManager::GetTimingChecks rather
// than as a pointer to it or a copy of it, for the reason ArmedCheck
// (simulator/timing_check_driver_internal.h) gives: the vector is appended to
// during the run, an append moves every element, and a copy would freeze a
// limit that §32.4.2's TIMINGCHECK annotation exists to change.
//
// Both edge times are kept, where the StabilityWindow of §31.3.1 and §31.3.2
// (src/simulator/timing_check_driver.cpp) keeps one. Table 31-3 and Table 31-6
// leave which event is the timecheck to which of the two occurs first, so
// neither signal is the one the other is always measured against.
struct StabilityPair {
  ArmedCheck armed;
  std::string ref_signal;
  std::string data_signal;
  bool has_ref = false;
  uint64_t ref_ticks = 0;
  bool has_data = false;
  uint64_t data_ticks = 0;
};

// §31.3.3's two messages. The check stands for two constraints, and the clause
// names each after its own limit: the setup limit bounds the window that ends
// at the reference edge and the hold limit the window that begins at it.
void ReportSetuphold(StabilitySide side, const StabilityPair& pair,
                     SimContext& ctx) {
  if (side == StabilitySide::kBefore) {
    ReportTimingViolation(
        std::format("$setuphold violation: data signal {} transitioned inside "
                    "the setup window ending at reference signal {}",
                    pair.data_signal, pair.ref_signal),
        "31.3.3", ctx);
    return;
  }
  ReportTimingViolation(
      std::format("$setuphold violation: data signal {} transitioned inside "
                  "the hold window beginning at reference signal {}",
                  pair.data_signal, pair.ref_signal),
      "31.3.3", ctx);
}

// §31.3.6's two messages, named for the two checks §31.3.6 makes $recrem
// equivalent to: the removal limit bounds the window that ends at the reference
// edge, as §31.3.4's own window does, and the recovery limit the window that
// begins at it, as §31.3.5's does.
void ReportRecrem(StabilitySide side, const StabilityPair& pair,
                  SimContext& ctx) {
  if (side == StabilitySide::kBefore) {
    ReportTimingViolation(
        std::format("$recrem violation: data signal {} transitioned inside the "
                    "removal window ending at reference signal {}",
                    pair.data_signal, pair.ref_signal),
        "31.3.6", ctx);
    return;
  }
  ReportTimingViolation(
      std::format("$recrem violation: data signal {} transitioned inside the "
                  "recovery window beginning at reference signal {}",
                  pair.data_signal, pair.ref_signal),
      "31.3.6", ctx);
}

// Reports the violation a check just detected, naming the signal that
// transitioned inside the window and the signal whose edge bounds it. The four
// kinds differ in which end of the window the reference edge is, which is why
// the messages differ in more than the name of the check.
void ReportViolation(TimingCheckKind kind, StabilitySide side,
                     const StabilityPair& pair, SimContext& ctx) {
  if (kind == TimingCheckKind::kSetuphold) {
    ReportSetuphold(side, pair, ctx);
    return;
  }
  if (kind == TimingCheckKind::kRecrem) {
    ReportRecrem(side, pair, ctx);
    return;
  }
  if (kind == TimingCheckKind::kRemoval) {
    ReportTimingViolation(
        std::format("$removal violation: data signal {} transitioned inside "
                    "the window ending at reference signal {}",
                    pair.data_signal, pair.ref_signal),
        "31.3.4", ctx);
    return;
  }
  ReportTimingViolation(
      std::format("$recovery violation: data signal {} transitioned inside the "
                  "window beginning at reference signal {}",
                  pair.data_signal, pair.ref_signal),
      "31.3.5", ctx);
}

// One of the two signals a §31.3 check names has just made its transition, and
// `event` says which. Reports a violation when the transition closes the
// check's window and the other signal's last transition falls inside it.
//
// Nothing is evaluated until both signals have transitioned at least once:
// §31.3 defines a window with respect to one transition and places the other
// inside it, so before the first of each there is no window and nothing to
// place.
void EvaluateStabilityPair(const StabilityPair& pair, StabilityEvent event,
                           SimContext& ctx) {
  if (!pair.has_ref || !pair.has_data) return;
  const TimingCheckEntry& check = pair.armed.Entry();
  if (!ClosesWindow(check.kind, event)) return;
  StabilitySide side =
      ViolatedSide(*pair.armed.mgr, check, pair.ref_ticks, pair.data_ticks);
  if (side == StabilitySide::kNone) return;
  ReportViolation(check.kind, side, pair, ctx);
  ToggleNotifier(check, ctx);
}

}  // namespace

void ArmStabilityPair(const SpecifyManager& mgr, std::size_t index,
                      SimContext& ctx) {
  const TimingCheckEntry& check = mgr.GetTimingChecks()[index];
  std::string ref_signal = check.inst_prefix + check.ref_signal;
  std::string data_signal = check.inst_prefix + check.data_signal;
  Variable* ref_var = ctx.FindVariable(ref_signal);
  Variable* data_var = ctx.FindVariable(data_signal);
  if (ref_var == nullptr || data_var == nullptr) return;
  SpecifyEdge ref_edge = check.ref_edge;
  SpecifyEdge data_edge = check.data_edge;
  auto pair = std::make_shared<StabilityPair>();
  pair->armed = ArmedCheck{&mgr, index};
  pair->ref_signal = std::move(ref_signal);
  pair->data_signal = std::move(data_signal);
  WatchEdge(ref_var, ref_edge, [pair, &ctx]() {
    pair->has_ref = true;
    pair->ref_ticks = ctx.CurrentTime().ticks;
    EvaluateStabilityPair(*pair, StabilityEvent::kReference, ctx);
  });
  WatchEdge(data_var, data_edge, [pair, &ctx]() {
    pair->has_data = true;
    pair->data_ticks = ctx.CurrentTime().ticks;
    EvaluateStabilityPair(*pair, StabilityEvent::kData, ctx);
  });
}

}  // namespace delta
