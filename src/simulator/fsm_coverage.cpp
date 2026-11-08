#include "simulator/fsm_coverage.h"

#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_fsm.h"
#include "simulator/code_coverage.h"
#include "simulator/coverage_control.h"
#include "simulator/lowerer_child.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vpi_coverage.h"
#include "simulator/vpi_design_walk.h"

namespace delta {

namespace {

std::optional<uint64_t> KnownValue(const Variable& var) {
  const Logic4Vec& value = var.value;
  for (uint32_t i = 0; i < value.nwords; ++i) {
    if (value.words[i].bval != 0) return std::nullopt;
  }
  return value.ToUint64();
}

std::optional<uint64_t> StateOf(const FsmCount& fsm) {
  uint64_t state = 0;
  for (const Variable* signal : fsm.signals) {
    const std::optional<uint64_t> kValue = KnownValue(*signal);
    if (!kValue) return std::nullopt;
    const uint32_t kWidth = std::min<uint32_t>(signal->value.width, 64);
    state = ((state << (kWidth / 2)) << (kWidth - (kWidth / 2))) | *kValue;
  }
  if (!fsm.select) return state;
  const int64_t kLow = std::min<int64_t>(fsm.select->first, 64);
  const int64_t kSpan =
      std::min<int64_t>(fsm.select->second - fsm.select->first + 1, 64);
  const uint64_t kMask = ~uint64_t{0} >> (64 - kSpan);
  return ((state >> (kLow / 2)) >> (kLow - (kLow / 2))) & kMask;
}

bool IsLegal(const FsmCount& fsm, uint64_t state) {
  return std::ranges::any_of(
      fsm.states, [state](const auto& named) { return named.second == state; });
}

std::int64_t LegalCount(const FsmCount& fsm) {
  std::unordered_set<uint64_t> values;
  for (const auto& named : fsm.states) values.insert(named.second);
  return static_cast<std::int64_t>(values.size());
}

void ApplyResets(InstanceFsms& inst, CoverageControlState& cov) {
  const std::uint64_t kStates =
      cov.ResetCount(inst.scope, kCoverageTypeFsmState);
  const std::uint64_t kMoves =
      cov.ResetCount(inst.scope, kCoverageTypeFsmTransition);
  for (FsmCount& fsm : inst.fsms) {
    if (kStates != inst.state_resets) fsm.visits.clear();
    if (kMoves != inst.transition_resets) fsm.transitions.clear();
  }
  inst.state_resets = kStates;
  inst.transition_resets = kMoves;
}

void Count(InstanceFsms& inst, CoverageControlState& cov) {
  ApplyResets(inst, cov);
  const bool kStates = cov.IsCollecting(inst.scope, kCoverageTypeFsmState);
  const bool kMoves = cov.IsCollecting(inst.scope, kCoverageTypeFsmTransition);
  std::int64_t reached = 0;
  std::int64_t moved = 0;
  for (FsmCount& fsm : inst.fsms) {
    const std::optional<uint64_t> kState = StateOf(fsm);
    if (kState && IsLegal(fsm, *kState)) {
      const bool kEntered = fsm.last != kState;
      if (kStates && (kEntered || !fsm.visits.contains(*kState))) {
        ++fsm.visits[*kState];
      }
      if (kMoves && kEntered && fsm.last) {
        fsm.transitions.emplace(*fsm.last, *kState);
      }
      fsm.last = kState;
    }
    reached += static_cast<std::int64_t>(fsm.visits.size());
    moved += static_cast<std::int64_t>(fsm.transitions.size());
  }
  cov.SetCoveredItems(inst.scope, kCoverageTypeFsmState, reached);
  cov.SetCoveredItems(inst.scope, kCoverageTypeFsmTransition, moved);
}

std::vector<std::pair<std::string_view, uint64_t>> LegalStates(
    const FsmDecl& decl, const std::string& prefix, SimContext& ctx) {
  std::vector<std::pair<std::string_view, uint64_t>> states;
  for (std::string_view state : decl.states) {
    const std::optional<uint64_t> kValue =
        KnownValue(*ctx.FindVariable(VpiFlatName(prefix, state)));
    if (kValue) states.emplace_back(state, *kValue);
  }
  return states;
}

std::optional<FsmCount> FsmOf(const FsmDecl& decl, const std::string& prefix,
                              SimContext& ctx) {
  FsmCount fsm;
  fsm.decl = decl;
  for (std::string_view name : decl.state_signals) {
    Variable* signal = ctx.FindVariable(VpiFlatName(prefix, name));
    if (signal == nullptr) return std::nullopt;
    fsm.signals.push_back(signal);
  }
  if (decl.has_part_select) {
    const PackedRange kRange = fsm.signals.front()->DeclaredRange();
    const int64_t kMsb = kRange.OffsetOf(decl.msb);
    const int64_t kLsb = kRange.OffsetOf(decl.lsb);
    fsm.select = std::make_pair(std::min(kMsb, kLsb), std::max(kMsb, kLsb));
  }
  fsm.states = LegalStates(decl, prefix, ctx);
  return fsm;
}

void ArmType(const InstanceFsms& inst, int type, std::int64_t count,
             CoverageControlState& cov) {
  cov.SetCoverableItems(inst.scope, type, count);
  cov.SetAvailability(inst.scope, type, CoverageAvailability::kFull);
  cov.Control(CoverageControl::kStart, type, inst.scope, false);
}

void AttachInstance(const RtlirModule& mod, const std::string& prefix,
                    SimContext& ctx) {
  CoverageControlState& cov = ctx.GetCoverageControlState();
  InstanceFsms& inst = cov.Code().fsm_instances.emplace_back();
  inst.prefix = prefix;
  inst.scope = CoverageScopeOfInstanceKey(prefix, ctx);
  std::int64_t legal = 0;
  std::int64_t moves = 0;
  for (const FsmDecl& decl : mod.fsms) {
    std::optional<FsmCount> fsm = FsmOf(decl, prefix, ctx);
    if (!fsm) continue;
    const std::int64_t kLegal = LegalCount(*fsm);
    legal += kLegal;
    moves += kLegal * (kLegal - 1);
    inst.fsms.push_back(std::move(*fsm));
  }
  if (inst.fsms.empty()) {
    cov.Code().fsm_instances.pop_back();
    return;
  }
  ArmType(inst, kCoverageTypeFsmState, legal, cov);
  ArmType(inst, kCoverageTypeFsmTransition, moves, cov);
  inst.state_resets = cov.ResetCount(inst.scope, kCoverageTypeFsmState);
  inst.transition_resets =
      cov.ResetCount(inst.scope, kCoverageTypeFsmTransition);
  for (const FsmCount& fsm : inst.fsms) {
    for (Variable* signal : fsm.signals) {
      signal->AddWatcher([&inst, &cov]() {
        Count(inst, cov);
        return false;
      });
    }
  }
  Count(inst, cov);
}

}  // namespace

void AttachFsmCoverage(const RtlirDesign* design, SimContext& ctx) {
  WalkInstancePaths(design,
                    [&ctx](const RtlirModule* mod, const std::string& prefix) {
                      if (!mod->fsms.empty()) AttachInstance(*mod, prefix, ctx);
                    });
}

EntityCoverage FsmHandleCoverage(const FsmHandleRef& handle,
                                 CoverageControlState& cov) {
  ApplyResets(*handle.instance, cov);
  const FsmCount& fsm = handle.instance->fsms[handle.fsm];
  EntityCoverage states;
  if (handle.state) {
    auto found = fsm.visits.find(*handle.state);
    states.total = 1;
    states.covered = found != fsm.visits.end() ? 1 : 0;
    states.hit_count = found != fsm.visits.end() ? found->second : 0;
    return states;
  }
  states.total = static_cast<std::uint64_t>(LegalCount(fsm));
  states.covered = fsm.visits.size();
  for (const auto& visit : fsm.visits) states.hit_count += visit.second;
  return states;
}

}  // namespace delta
