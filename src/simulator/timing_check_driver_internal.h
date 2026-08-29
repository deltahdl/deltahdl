#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"
#include "simulator/variable.h"

namespace delta {

// What every Clause 31 check needs to watch a signal and report against it,
// shared by the four files that arm the twelve checks: §31.3's stability
// windows in simulator/timing_check_driver.cpp and
// simulator/timing_check_stability.cpp, §31.4.4's $width, §31.4.5's $period and
// §31.4.6's $nochange in simulator/timing_check_pulse.cpp, and §31.4.1 through
// §31.4.3's skew family in simulator/timing_check_skew.cpp.
//
// The twelve checks divide by what they measure between, not by what they do
// once they find a violation, which is why the reporting and the notifier live
// here and the window arithmetic does not. Each file restates the arithmetic of
// its own clauses rather than calling the SpecifyManager::Check*Violation
// members: those select a check by the spelling of its signals, with no
// comparison of TimingCheckEntry::inst_prefix, so with one check registered per
// module instance a single call answers for every instance of the cell. A
// watcher already knows which entry it was armed for.

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
inline EdgeLevel LevelOfLsb(const Logic4Vec& v) {
  if (v.nwords == 0) return EdgeLevel::kAbsent;
  if ((v.words[0].bval & 1U) != 0U) return EdgeLevel::kUnknown;
  return (v.words[0].aval & 1U) != 0U ? EdgeLevel::kOne : EdgeLevel::kZero;
}

// The level one half of an edge_descriptor names. TimingCheckEntry holds only
// the '0', '1' and 'x' that BuildTimingCheckUnderOptions
// (simulator/specify_timing_check.cpp) folded z and the upper-case spellings
// into, so anything that is not '0' or '1' is the x §31.5 treats z as.
inline EdgeLevel LevelOfDescriptorChar(char c) {
  if (c == '0') return EdgeLevel::kZero;
  if (c == '1') return EdgeLevel::kOne;
  return EdgeLevel::kUnknown;
}

// §31.5's edge_control_specifier as a watcher matches it: the shorthand the
// timing_check_event was written with, together with the edge_descriptor list
// where the general form was written instead. §31.5 gives the two forms
// separately -- posedge is a shorthand for edge[01, 0x, x1] rather than a
// second name for it -- and the parser records which was written, so both
// travel to the watcher and TimingCheckEdgeMatches picks between them.
//
// The list is held by value because a watcher outlives the arming call:
// WatchEdge moves it into the lambda it installs on the variable, which fires
// for the rest of the run.
struct TimingCheckEdge {
  SpecifyEdge edge = SpecifyEdge::kNone;
  std::vector<std::pair<char, char>> descriptors;
};

// The edge_control_specifier of a check's reference_event and of its
// data_event, read off the entry the two were built into.
inline TimingCheckEdge RefEdgeOf(const TimingCheckEntry& check) {
  return TimingCheckEdge{check.ref_edge, check.ref_edge_descriptors};
}

inline TimingCheckEdge DataEdgeOf(const TimingCheckEntry& check) {
  return TimingCheckEdge{check.data_edge, check.data_edge_descriptors};
}

// Whether a change from `from` to `to` is a transition `edge` names. A value
// that did not change is no transition at all and is never one.
//
// An edge_control_specifier written in the general form names its transitions
// outright, and §31.5 admits six of them -- 01, 0x, 10, 1x, x0 and x1 -- so the
// list is compared against the two levels directly and a transition it does not
// list is not the event. The list is what decides wherever one was written,
// SpecifyEdge::kEdge saying only that the general form was used.
//
// Where no list was written, §31.5 makes posedge the shorthand for edge[01, 0x,
// x1] and negedge the shorthand for edge[10, x0, 1x], so posedge is every
// transition that leaves 0 or arrives at 1, and negedge every transition that
// leaves 1 or arrives at 0.
//
// SpecifyEdge::kNone is a timing_check_event written without an
// edge_control_specifier, which Syntax 31-2 (§31.2) allows and which no edge
// restricts, so every transition matches it.
inline bool TimingCheckEdgeMatches(const TimingCheckEdge& edge, EdgeLevel from,
                                   EdgeLevel to) {
  if (from == EdgeLevel::kAbsent || to == EdgeLevel::kAbsent) return false;
  if (from == to) return false;
  if (!edge.descriptors.empty()) {
    for (const std::pair<char, char>& descriptor : edge.descriptors) {
      if (LevelOfDescriptorChar(descriptor.first) == from &&
          LevelOfDescriptorChar(descriptor.second) == to) {
        return true;
      }
    }
    return false;
  }
  if (edge.edge == SpecifyEdge::kPosedge) {
    return from == EdgeLevel::kZero || to == EdgeLevel::kOne;
  }
  if (edge.edge == SpecifyEdge::kNegedge) {
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
inline void WatchEdge(Variable* var, TimingCheckEdge edge,
                      std::function<void()> on_edge) {
  auto seen = std::make_shared<EdgeLevel>(LevelOfLsb(var->value));
  var->AddWatcher(
      [var, edge = std::move(edge), seen, on_edge = std::move(on_edge)]() {
        EdgeLevel before = *seen;
        *seen = LevelOfLsb(var->value);
        if (TimingCheckEdgeMatches(edge, before, *seen)) on_edge();
        return false;
      });
}

// Which entry a watcher was armed for, held as a position in
// SpecifyManager::GetTimingChecks rather than as a pointer to it or a copy of
// it. A pointer would dangle, because SpecifyManager::AddTimingCheck appends to
// that vector during the run -- §32.9's $sdf_annotate registers what an SDF
// file names -- and an append moves every element. A copy would freeze the
// limit, and §32.4.2's TIMINGCHECK annotation exists to change it; reading the
// entry back at every timecheck event is what lets an annotation reach a check
// already armed.
struct ArmedCheck {
  const SpecifyManager* mgr = nullptr;
  std::size_t index = 0;

  const TimingCheckEntry& Entry() const {
    return mgr->GetTimingChecks()[index];
  }
};

// §31.7: whether a timing_check_event that just happened enables the check it
// belongs to. A conditioned event "ties the occurrence of timing checks to the
// value of a conditioning signal", so an event whose condition does not hold is
// not an occurrence of the check at all and neither opens a window nor closes
// one. `condition` is the expression the event was declared with, null for an
// unconditioned event, which always enables.
//
// Three rules of §31.7 are applied, and each is applied where it is stated:
// TimingCheckConditioningSignal picks out the operand the clause calls the
// conditioning signal, the least significant word of its value is what
// TimingCheckConditionEnables is handed because "if a vector net or an
// expression resulting in a multibit value is used, then the LSB ... is used",
// and TimingCheckConditionEnables settles the six forms of Syntax 31-16
// together with the x rule -- deterministic comparisons are disabled by an x on
// the conditioning signal, nondeterministic ones enabled by it. A value with no
// words states no bit, and states no true condition either;
// ConditionalPathIsActive in src/simulator/module_path_delay.cpp answers
// §30.4.4.1 the same way.
//
// The evaluation stands in the instance whose specify block declared the check,
// which `inst_prefix` names. §31.7 has the conditioning signal written by the
// declaring module's bare name, and SimContext would otherwise join that name
// to the prefix of whatever process is running -- here the process that
// committed the transition, which is in no particular instance relation to the
// check.
inline bool TimingCheckEventEnabled(const Expr* condition,
                                    std::string_view inst_prefix,
                                    SimContext& ctx) {
  if (condition == nullptr) return true;
  InstancePrefixOverride scope(ctx.InstancePrefixOverride(), inst_prefix);
  const Expr* signal = TimingCheckConditioningSignal(condition);
  Logic4Vec value = EvalExpr(signal, ctx, ctx.GetArena());
  if (value.nwords == 0) return false;
  TimingCheckConditionClass form = ClassifyTimingCheckCondition(condition);
  return TimingCheckConditionEnables(form.kind, value.words[0],
                                     form.scalar_constant_bit);
}

// §31.7: one check's conditioned event -- which check, and which of its two
// timing_check_events, so that the `&&&` condition gating the event can be read
// off the entry at the moment a transition arrives rather than copied when the
// watcher was armed. Reading it back is what lets §32.4.2's TIMINGCHECK
// annotation reach a check already armed, for the reason ArmedCheck holds a
// position rather than a pointer.
struct ConditionedEvent {
  ArmedCheck armed;
  bool is_data_event = false;

  const Expr* Condition() const {
    const TimingCheckEntry& check = armed.Entry();
    return is_data_event ? check.data_condition_expr : check.ref_condition_expr;
  }
};

// Arms the watcher WatchEdge arms and calls `on_edge` only for a transition
// that §31.7 makes an occurrence of the check. Every §31 watcher goes through
// this rather than through WatchEdge: an event written without a `&&&`
// condition carries a null one and is enabled unconditionally, so there is no
// second case to keep.
inline void WatchConditionedEdge(Variable* var, TimingCheckEdge edge,
                                 ConditionedEvent event, SimContext& ctx,
                                 std::function<void()> on_edge) {
  WatchEdge(
      var, std::move(edge), [event, &ctx, on_edge = std::move(on_edge)]() {
        if (!TimingCheckEventEnabled(event.Condition(),
                                     event.armed.Entry().inst_prefix, ctx)) {
          return;
        }
        on_edge();
      });
}

// The two timing_check_events a check writes in its own arguments, armed with
// one watcher each. §31.3's six checks and §31.4.1 through §31.4.3's three each
// write a reference_event and a data_event of their own, so both events carry a
// signal, a §31.5 edge_control_specifier and a §31.7 `&&&` condition the
// declaration named. §31.4.4's $width, §31.4.5's $period and §31.4.6's
// $nochange derive one of their two edges from the other and do not go through
// this.
//
// `on_ref` runs when the reference_event occurs and `on_data` when the
// data_event does, each already gated by the edge_control_specifier and the
// condition its own event was written with.
//
// Nothing is armed when either signal names no variable of the design, which is
// what a check whose specify block was registered for a module the design never
// elaborated leaves behind. Both callbacks are dropped in that case and the
// returned names are empty.
//
// The two signal names are returned rather than written into the caller's
// state, because the callbacks close over that state and it therefore exists
// before this is called.
struct ArmedTimingCheckEvents {
  std::string ref_signal;
  std::string data_signal;
};

inline ArmedTimingCheckEvents ArmTimingCheckEvents(
    ArmedCheck armed, SimContext& ctx, const std::function<void()>& on_ref,
    const std::function<void()>& on_data) {
  const TimingCheckEntry& check = armed.Entry();
  std::string ref_signal = check.inst_prefix + check.ref_signal;
  std::string data_signal = check.inst_prefix + check.data_signal;
  Variable* ref_var = ctx.FindVariable(ref_signal);
  Variable* data_var = ctx.FindVariable(data_signal);
  if (ref_var == nullptr || data_var == nullptr) return {};
  WatchConditionedEdge(ref_var, RefEdgeOf(check),
                       ConditionedEvent{armed, /*is_data_event=*/false}, ctx,
                       on_ref);
  WatchConditionedEdge(data_var, DataEdgeOf(check),
                       ConditionedEvent{armed, /*is_data_event=*/true}, ctx,
                       on_data);
  return ArmedTimingCheckEvents{std::move(ref_signal), std::move(data_signal)};
}

// Reports one violation as a warning. §31.2's violation is a state the run
// reached rather than a construct that is illegal, which is why it is a warning
// and not an error, and it stands at SourceLoc::None() because TimingCheckEntry
// records no source position for the declaration it was built from.
inline void ReportTimingViolation(std::string_view message,
                                  std::string_view subclause, SimContext& ctx) {
  ctx.GetDiag().Warning(SourceLoc::None(), std::string(message),
                        Subclause(std::string(subclause)));
}

// §31.6: "Whenever a timing violation occurs, the timing check updates the
// value of the notifier", and Table 31-13 gives the value it updates to.
// ToggleNotifierOnViolation (src/simulator/specify_timing_check.h) is that
// table. §31.6 has the notifier "declared in the module where timing check
// tasks are invoked", which is the module whose specify block declared the
// check, so it is looked up under the same instance prefix the check's signals
// are.
//
// Only the least significant bit is written and the rest of the variable is
// left as it stands, Table 31-13 stating one value and §31.6's notifier being a
// scalar. The write goes through Variable::NotifyWatchers because §31.6 has a
// model "use the notifier to make behavior a function of timing check
// violations", and an `always @(notifier)` sees the new value only once the
// watchers have been notified.
inline void ToggleNotifier(const TimingCheckEntry& check, SimContext& ctx) {
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

}  // namespace delta
