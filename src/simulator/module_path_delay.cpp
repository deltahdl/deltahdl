// The selection half of simulator/module_path_delay.h: which of Table 30-2's
// twelve transitions a change of value is, and which registered module path
// governs that change. RunModulePathTransition, declared in the same header, is
// in simulator/module_path_drive.cpp.

#include "simulator/module_path_delay.h"

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

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

// Whether `pd` starts at one of the driver's operands, which is what makes it a
// path the transition may be reached through.
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
    if (pd.dst_port == output) return true;
  }
  return false;
}

ModulePathDelay SelectModulePathDelay(
    const SpecifyManager& mgr, std::string_view output,
    const std::vector<std::string_view>& sources, const Logic4Vec& from,
    const Logic4Vec& to) {
  uint8_t slot = ModulePathTransitionSlot(from, to);
  ModulePathDelay selected;
  for (const PathDelay& pd : mgr.GetPathDelays()) {
    if (pd.dst_port != output) continue;
    if (!PathStartsAtOneOf(pd, sources)) continue;
    // §30.5.3: "comparing the correct delay for the specific transition being
    // scheduled from each specify path and choosing the smallest".
    if (selected.found && pd.delays[slot] >= selected.delay) continue;
    // §30.7's two limits are read from the path the delay was taken from, so a
    // caller measures a pulse against the limits of the delay it got.
    selected = ModulePathDelay{true, pd.delays[slot], pd.reject_limit[slot],
                               pd.error_limit[slot]};
  }
  return selected;
}

}  // namespace delta
