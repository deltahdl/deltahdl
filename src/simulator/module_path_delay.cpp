#include "simulator/module_path_delay.h"

#include <algorithm>
#include <bit>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <system_error>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/variable.h"

namespace delta {
namespace {

enum class PathLevel : uint8_t {
  kZero = 0,
  kOne = 1,
  kX = 2,
  kZ = 3,
};

constexpr uint8_t kTransitionSlots[4][4] = {
    {0, 0, 6, 2},
    {1, 0, 8, 4},
    {9, 7, 0, 10},
    {5, 3, 11, 0},
};

bool IsHighZValue(const Logic4Vec& v) {
  if (v.nwords == 0) return false;
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].aval != 0) return false;
    if (v.words[i].bval == 0) return false;
  }
  return true;
}

PathLevel LevelOf(const Logic4Vec& v) {
  if (IsHighZValue(v)) return PathLevel::kZ;
  if (HasUnknownBits(v)) return PathLevel::kX;
  if (v.IsTruthy()) return PathLevel::kOne;
  return PathLevel::kZero;
}

bool PathEndsAt(const PathDelay& pd, std::string_view qualified) {
  if (qualified.size() != pd.inst_prefix.size() + pd.dst_port.size()) {
    return false;
  }
  return qualified.substr(0, pd.inst_prefix.size()) == pd.inst_prefix &&
         qualified.substr(pd.inst_prefix.size()) == pd.dst_port;
}

bool PathStartsAtOneOf(const PathDelay& pd,
                       const std::vector<std::string_view>& sources) {
  for (std::string_view src : sources) {
    if (pd.src_port == src) return true;
  }
  return false;
}

bool SelectBounds(std::string_view select, int64_t& left, int64_t& right) {
  if (select.size() < 3 || select.front() != '[' || select.back() != ']')
    return false;
  select = select.substr(1, select.size() - 2);
  const size_t kColon = select.find(':');
  std::string_view lhs = select.substr(0, kColon);
  std::string_view rhs =
      kColon == std::string_view::npos ? lhs : select.substr(kColon + 1);
  auto parse = [](std::string_view text, int64_t& out) {
    auto [stop, ec] =
        std::from_chars(text.data(), text.data() + text.size(), out);
    return ec == std::errc() && stop == text.data() + text.size();
  };
  return parse(lhs, left) && parse(rhs, right);
}

uint8_t BitLevel(const Logic4Word& word, unsigned bit) {
  if (((word.bval >> bit) & 1U) != 0U) return 2;
  return static_cast<uint8_t>((word.aval >> bit) & 1U);
}

uint8_t EdgeBetween(uint8_t from, uint8_t to) {
  if (from == to) return 0;
  if (from == 0 || to == 1) return Variable::kEdgeRise;
  return Variable::kEdgeFall;
}

uint8_t LsbEdge(const std::vector<Logic4Word>& seen, const Variable& var) {
  if (var.value.nwords == 0 || seen.empty()) return 0;
  return EdgeBetween(BitLevel(seen[0], 0), BitLevel(var.value.words[0], 0));
}

void RecordChangedBits(Variable& var, const std::vector<Logic4Word>& seen,
                       uint64_t now) {
  const size_t kWords = std::min<size_t>(var.value.nwords, seen.size());
  for (size_t i = 0; i < kWords; ++i) {
    uint64_t diff = (var.value.words[i].aval ^ seen[i].aval) |
                    (var.value.words[i].bval ^ seen[i].bval);
    while (diff != 0) {
      const auto kBit = static_cast<unsigned>(std::countr_zero(diff));
      const size_t kOffset = i * 64 + kBit;
      if (kOffset < var.bit_change_ticks.size()) {
        var.bit_change_ticks[kOffset] = now;
        var.bit_change_edges[kOffset] = EdgeBetween(
            BitLevel(seen[i], kBit), BitLevel(var.value.words[i], kBit));
      }
      diff &= diff - 1;
    }
  }
}

}  // namespace

uint8_t ModulePathTransitionSlot(const Logic4Vec& from, const Logic4Vec& to) {
  auto from_level = static_cast<uint8_t>(LevelOf(from));
  auto to_level = static_cast<uint8_t>(LevelOf(to));
  return kTransitionSlots[from_level][to_level];
}

std::vector<std::string> ModulePathSourcesOf(const SpecifyManager& mgr,
                                             std::string_view output) {
  std::vector<std::string> sources;
  for (const PathDelay& pd : mgr.GetPathDelays()) {
    if (!PathEndsAt(pd, output)) continue;
    std::string name = pd.inst_prefix + pd.src_port;
    if (std::find(sources.begin(), sources.end(), name) == sources.end()) {
      sources.push_back(std::move(name));
    }
  }
  return sources;
}

bool IsModulePathOutput(const SpecifyManager& mgr, std::string_view output) {
  for (const PathDelay& pd : mgr.GetPathDelays()) {
    if (PathEndsAt(pd, output)) return true;
  }
  return false;
}

static uint64_t SourceChangeTicks(const PathDelay& pd, SimContext& ctx) {
  const Variable* var = ctx.FindVariable(pd.inst_prefix + pd.src_port);
  if (var == nullptr) return 0;
  int64_t left = 0;
  int64_t right = 0;
  if (var->bit_change_ticks.empty() ||
      !SelectBounds(pd.src_select, left, right)) {
    return var->last_change_ticks;
  }
  const PackedRange kRange = var->DeclaredRange();
  uint64_t latest = 0;
  for (int64_t idx = std::min(left, right); idx <= std::max(left, right);
       ++idx) {
    if (!kRange.Contains(idx)) continue;
    auto offset = static_cast<size_t>(kRange.OffsetOf(idx));
    if (offset < var->bit_change_ticks.size())
      latest = std::max(latest, var->bit_change_ticks[offset]);
  }
  return latest;
}

static bool ConditionalPathIsActive(const PathDelay& pd,
                                    const ModulePathDrive& drive) {
  if (pd.condition_expr == nullptr) return true;
  InstancePrefixOverride scope(drive.ctx.InstancePrefixOverride(),
                               pd.inst_prefix);
  Logic4Vec value = EvalExpr(pd.condition_expr, drive.ctx, drive.arena);
  if (value.nwords == 0) return false;
  return StateDependentPathConditionEnables(value.words[0]);
}

static bool CorrespondingConditionIsTrue(
    const std::vector<PathCandidate>& candidates,
    const PathDelay& ifnone_path) {
  for (const PathCandidate& candidate : candidates) {
    const PathDelay& pd = *candidate.path;
    if (pd.is_ifnone || pd.condition_expr == nullptr) continue;
    if (pd.src_port != ifnone_path.src_port) continue;
    if (pd.dst_port != ifnone_path.dst_port) continue;
    if (candidate.condition_true) return true;
  }
  return false;
}

static void SettleIfnoneCandidates(std::vector<PathCandidate>& candidates) {
  for (PathCandidate& candidate : candidates) {
    if (!candidate.path->is_ifnone) continue;
    candidate.condition_true =
        !CorrespondingConditionIsTrue(candidates, *candidate.path);
  }
}

static bool EdgeSensitivePathIsActive(const PathDelay& pd, SimContext& ctx) {
  if (pd.edge == SpecifyEdge::kNone) return true;
  const Variable* var = ctx.FindVariable(pd.inst_prefix + pd.src_port);
  if (var == nullptr) return true;
  uint8_t edge = var->last_change_edge;
  int64_t left = 0;
  int64_t right = 0;
  if (!var->bit_change_edges.empty() &&
      SelectBounds(pd.src_select, left, right)) {
    const PackedRange kRange = var->DeclaredRange();
    const int64_t kLsb =
        kRange.OffsetOf(left) < kRange.OffsetOf(right) ? left : right;
    const auto kOffset = static_cast<size_t>(kRange.OffsetOf(kLsb));
    edge = kOffset < var->bit_change_edges.size()
               ? var->bit_change_edges[kOffset]
               : 0;
  }
  if (pd.edge == SpecifyEdge::kPosedge) return edge == Variable::kEdgeRise;
  if (pd.edge == SpecifyEdge::kNegedge) return edge == Variable::kEdgeFall;
  return edge != 0;
}

ModulePathDelay SelectModulePathDelay(const ModulePathDrive& drive,
                                      const Logic4Vec& from,
                                      const Logic4Vec& to) {
  uint8_t slot = ModulePathTransitionSlot(from, to);
  std::vector<PathCandidate> candidates;
  for (const PathDelay& pd : drive.mgr.GetPathDelays()) {
    if (!PathEndsAt(pd, drive.output)) continue;
    if (!drive.at_port && !PathStartsAtOneOf(pd, drive.sources)) continue;
    bool active = (pd.is_ifnone || ConditionalPathIsActive(pd, drive)) &&
                  EdgeSensitivePathIsActive(pd, drive.ctx);
    candidates.push_back(
        PathCandidate{&pd, SourceChangeTicks(pd, drive.ctx), active});
  }
  SettleIfnoneCandidates(candidates);
  const PathDelay* selected = SelectActivePath(candidates, slot);
  if (selected == nullptr) return ModulePathDelay{};
  uint64_t source_ticks = 0;
  for (const PathCandidate& candidate : candidates) {
    if (candidate.path == selected)
      source_ticks = candidate.last_transition_time;
  }
  const uint64_t kDelay = selected->delays[slot];
  return ModulePathDelay{
      true, kDelay, EffectivePulseLimit(selected->reject_limit[slot], kDelay),
      EffectivePulseLimit(selected->error_limit[slot], kDelay), source_ticks};
}

static void WatchSourceVariable(Variable* var, SimContext& ctx, bool per_bit) {
  if (per_bit) {
    var->bit_change_ticks.assign(var->value.width, 0);
    var->bit_change_edges.assign(var->value.width, 0);
  }
  auto seen = std::make_shared<std::vector<Logic4Word>>(
      var->value.words, var->value.words + var->value.nwords);
  var->AddWatcher([var, &ctx, seen]() {
    bool changed = var->value.nwords != seen->size();
    for (uint32_t i = 0; !changed && i < var->value.nwords; ++i) {
      changed = var->value.words[i].aval != (*seen)[i].aval ||
                var->value.words[i].bval != (*seen)[i].bval;
    }
    if (changed) {
      const uint64_t kNow = ctx.CurrentTime().ticks;
      if (!var->bit_change_ticks.empty()) RecordChangedBits(*var, *seen, kNow);
      var->last_change_edge = LsbEdge(*seen, *var);
      seen->assign(var->value.words, var->value.words + var->value.nwords);
      var->last_change_ticks = kNow;
    }
    return false;
  });
}

void WatchModulePathSources(const SpecifyManager& mgr, SimContext& ctx) {
  std::unordered_map<std::string, bool> sources;
  for (const PathDelay& pd : mgr.GetPathDelays()) {
    bool& per_bit = sources[pd.inst_prefix + pd.src_port];
    per_bit = per_bit || !pd.src_select.empty();
  }
  for (const auto& [qualified, per_bit] : sources) {
    Variable* var = ctx.FindVariable(qualified);
    if (var != nullptr) WatchSourceVariable(var, ctx, per_bit);
  }
}

}  // namespace delta
