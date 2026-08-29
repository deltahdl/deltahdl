// The selection half of simulator/module_path_delay.h: which of Table 30-2's
// twelve transitions a change of value is, and which registered module path
// governs that change. RunModulePathTransition, declared in the same header, is
// in simulator/module_path_drive.cpp.

#include "simulator/module_path_delay.h"

#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// The four levels Table 30-2's rows and columns run over. The enumerator values
// are the indices into kTransitionSlots.
enum class PathLevel : uint8_t {
  kZero = 0,
  kOne = 1,
  kX = 2,
  kZ = 3,
};

// Table 30-2's slots, indexed [from level][to level]. The table lists the
// twelve transitions in the order 0 -> 1, 1 -> 0, 0 -> z, z -> 1, 1 -> z, z ->
// 0, 0 -> x, x -> 1, 1 -> x, x -> 0, x -> z, z -> x, which is what puts 6 at 0
// -> x and 11 at z -> x. The diagonal is not a transition and answers slot 0.
constexpr uint8_t kTransitionSlots[4][4] = {
    {0, 0, 6, 2},
    {1, 0, 8, 4},
    {9, 7, 0, 10},
    {5, 3, 11, 0},
};

// Every bit high-z. simulator/evaluation.h declares HasUnknownBits and no
// counterpart for z, so the test stands here; SelectScalarContAssignDelay in
// simulator/lowerer_contassign.cpp asks the same question of a continuous
// assignment's value.
bool IsHighZValue(const Logic4Vec& v) {
  if (v.nwords == 0) return false;
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].aval != 0) return false;
    if (v.words[i].bval == 0) return false;
  }
  return true;
}

// The level Table 30-2 reduces a vector to. The z test comes before the x test
// because HasUnknownBits reports any bval bit, and z sets bval as x does.
PathLevel LevelOf(const Logic4Vec& v) {
  if (IsHighZValue(v)) return PathLevel::kZ;
  if (HasUnknownBits(v)) return PathLevel::kX;
  if (v.IsTruthy()) return PathLevel::kOne;
  return PathLevel::kZero;
}

// Whether `pd` ends at the module path destination `qualified` names, which is
// that destination's own port name under the instance prefix of the module
// whose specify block declared the path. The two halves are compared where they
// stand rather than joined into one string, so a lookup allocates nothing.
bool PathEndsAt(const PathDelay& pd, std::string_view qualified) {
  if (qualified.size() != pd.inst_prefix.size() + pd.dst_port.size()) {
    return false;
  }
  return qualified.substr(0, pd.inst_prefix.size()) == pd.inst_prefix &&
         qualified.substr(pd.inst_prefix.size()) == pd.dst_port;
}

// Whether `pd` starts at one of the driver's operands, which is what makes it a
// path the transition may be reached through. The operands are the bare names
// the driver was written with, and pd.src_port is the bare name the specify
// block was written with; both stand in the instance PathEndsAt has already
// selected, so no prefix enters here.
bool PathStartsAtOneOf(const PathDelay& pd,
                       const std::vector<std::string_view>& sources) {
  for (std::string_view src : sources) {
    if (pd.src_port == src) return true;
  }
  return false;
}

}  // namespace

uint8_t ModulePathTransitionSlot(const Logic4Vec& from, const Logic4Vec& to) {
  auto from_level = static_cast<uint8_t>(LevelOf(from));
  auto to_level = static_cast<uint8_t>(LevelOf(to));
  return kTransitionSlots[from_level][to_level];
}

bool IsModulePathOutput(const SpecifyManager& mgr, std::string_view output) {
  for (const PathDelay& pd : mgr.GetPathDelays()) {
    if (PathEndsAt(pd, output)) return true;
  }
  return false;
}

// The time the source terminal of `pd` last changed, or 0 where the design
// declares no such variable. The name handed to FindVariable is already
// qualified, and that resolves from inside the instance that declared the path
// because SimContext::FindVariable reads a dotted name out of its own table
// rather than joining it to the running process's prefix -- the rule §23.8's
// hierarchical names need and this relies on. Zero is also what a source that
// has never changed reads, and the two need not be told apart: §30.5.3 compares
// these times against each other, and a source that never moved is never the
// most recent unless every candidate is in the same position.
static uint64_t SourceChangeTicks(const PathDelay& pd, SimContext& ctx) {
  const Variable* var = ctx.FindVariable(pd.inst_prefix + pd.src_port);
  return var != nullptr ? var->last_change_ticks : 0;
}

ModulePathDelay SelectModulePathDelay(const ModulePathDrive& drive,
                                      const Logic4Vec& from,
                                      const Logic4Vec& to) {
  uint8_t slot = ModulePathTransitionSlot(from, to);
  std::vector<PathCandidate> candidates;
  for (const PathDelay& pd : drive.mgr.GetPathDelays()) {
    if (!PathEndsAt(pd, drive.output)) continue;
    if (!PathStartsAtOneOf(pd, drive.sources)) continue;
    candidates.push_back(PathCandidate{&pd, SourceChangeTicks(pd, drive.ctx),
                                       /*condition_true=*/true});
  }
  const PathDelay* selected = SelectActivePath(candidates, slot);
  if (selected == nullptr) return ModulePathDelay{};
  // §30.7 measures a pulse against the limits of the delay that formed its
  // edge, so all three are read off the one path the selection settled on.
  return ModulePathDelay{true, selected->delays[slot],
                         selected->reject_limit[slot],
                         selected->error_limit[slot]};
}

// Records on `var` the time its value last changed, for as long as the run
// lasts. Variable::last_change_ticks has no other writer.
//
// The watcher keeps its own copy of the value it last recorded rather than
// trusting that a notification means a change. Variable::NotifyWatchers fires
// whenever a driver commits, and a driver may commit the value already there --
// Net::Resolve in src/simulator/net.cpp notifies after every resolution. A time
// recorded for a commit that changed nothing would make that path the more
// recent of two and hand the transition the wrong delay, which is the very
// mistake §30.5.3 is being applied to avoid.
//
// It returns false so that NotifyWatchers re-arms it: a module path source may
// transition any number of times before the run ends.
static void WatchSourceVariable(Variable* var, SimContext& ctx) {
  auto seen = std::make_shared<std::vector<Logic4Word>>(
      var->value.words, var->value.words + var->value.nwords);
  var->AddWatcher([var, &ctx, seen]() {
    bool changed = var->value.nwords != seen->size();
    for (uint32_t i = 0; !changed && i < var->value.nwords; ++i) {
      changed = var->value.words[i].aval != (*seen)[i].aval ||
                var->value.words[i].bval != (*seen)[i].bval;
    }
    if (changed) {
      seen->assign(var->value.words, var->value.words + var->value.nwords);
      var->last_change_ticks = ctx.CurrentTime().ticks;
    }
    return false;
  });
}

void WatchModulePathSources(const SpecifyManager& mgr, SimContext& ctx) {
  // One watcher per source terminal however many paths start there, since the
  // time recorded is the variable's and not the path's.
  std::unordered_set<std::string> armed;
  for (const PathDelay& pd : mgr.GetPathDelays()) {
    std::string qualified = pd.inst_prefix + pd.src_port;
    if (!armed.insert(qualified).second) continue;
    Variable* var = ctx.FindVariable(qualified);
    if (var != nullptr) WatchSourceVariable(var, ctx);
  }
}

}  // namespace delta
