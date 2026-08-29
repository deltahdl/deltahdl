#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <string_view>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_specify.h"
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
inline bool TimingCheckEdgeMatches(SpecifyEdge edge, EdgeLevel from,
                                   EdgeLevel to) {
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
inline void WatchEdge(Variable* var, SpecifyEdge edge,
                      std::function<void()> on_edge) {
  auto seen = std::make_shared<EdgeLevel>(LevelOfLsb(var->value));
  var->AddWatcher([var, edge, seen, on_edge = std::move(on_edge)]() {
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
