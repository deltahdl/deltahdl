#include "simulator/fsm_coverage.h"

#include <algorithm>
#include <cstdint>
#include <memory>
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
#include "simulator/coverage_control.h"
#include "simulator/lowerer_child.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_walk.h"

namespace delta {

namespace {

// One FSM of one instance: the signals holding its current state, the bits of
// the one signal a part-select holds it in, its legal state values and those
// of them it has reached.
struct FsmCount {
  std::vector<Variable*> signals;
  std::optional<std::pair<int64_t, int64_t>> select;  // low and high offset
  std::unordered_set<uint64_t> legal;
  std::unordered_set<uint64_t> reached;
};

// The FSMs of one instance, counted together as the instance's coverage, and
// the number of resets of the instance already applied to their counts.
struct InstanceFsms {
  std::string scope;
  std::vector<FsmCount> fsms;
  std::uint64_t resets = 0;
};

// The value `var` holds, or nothing where any bit of it is x or z, which no
// legal state is.
std::optional<uint64_t> KnownValue(const Variable& var) {
  const Logic4Vec& value = var.value;
  for (uint32_t i = 0; i < value.nwords; ++i) {
    if (value.words[i].bval != 0) return std::nullopt;
  }
  return value.ToUint64();
}

// §40.4.1 to §40.4.3: the state `fsm` holds: its signal's value, the bits of
// it a part-select names, or its signals' values concatenated, the first one
// listed the most significant; nothing where a bit is x or z.
std::optional<uint64_t> StateOf(const FsmCount& fsm) {
  uint64_t state = 0;
  for (const Variable* signal : fsm.signals) {
    const std::optional<uint64_t> kValue = KnownValue(*signal);
    if (!kValue) return std::nullopt;
    const uint32_t kWidth = std::min<uint32_t>(signal->value.width, 64);
    state = kWidth >= 64 ? *kValue : (state << kWidth) | *kValue;
  }
  if (!fsm.select) return state;
  const int64_t kLow = fsm.select->first;
  const int64_t kSpan = fsm.select->second - kLow + 1;
  const uint64_t kMask =
      kSpan >= 64 ? ~uint64_t{0} : (uint64_t{1} << kSpan) - 1;
  return kLow >= 64 ? 0 : (state >> kLow) & kMask;
}

// §40.3.2.3 with §40.3.2.1: count the state each FSM of `inst` holds where
// it is a legal one and the instance is collecting, starting the count over
// where the instance was reset since, and report the states reached so far.
void Count(InstanceFsms& inst, CoverageControlState& cov) {
  if (cov.ResetCount(inst.scope) != inst.resets) {
    inst.resets = cov.ResetCount(inst.scope);
    for (FsmCount& fsm : inst.fsms) fsm.reached.clear();
  }
  if (!cov.IsCollecting(inst.scope)) return;
  std::int64_t reached = 0;
  for (FsmCount& fsm : inst.fsms) {
    const std::optional<uint64_t> kState = StateOf(fsm);
    if (kState && fsm.legal.contains(*kState)) fsm.reached.insert(*kState);
    reached += static_cast<std::int64_t>(fsm.reached.size());
  }
  cov.SetCoveredItems(inst.scope, kCoverageTypeFsmState, reached);
}

// §40.4.6: the legal state values of `decl` in the instance keyed `prefix`,
// the values its state parameters hold there, each once.
std::unordered_set<uint64_t> LegalStates(const FsmDecl& decl,
                                         const std::string& prefix,
                                         SimContext& ctx) {
  std::unordered_set<uint64_t> legal;
  for (std::string_view state : decl.states) {
    const Variable* param = ctx.FindVariable(VpiFlatName(prefix, state));
    const std::optional<uint64_t> kValue =
        param != nullptr ? KnownValue(*param) : std::nullopt;
    if (kValue) legal.insert(*kValue);
  }
  return legal;
}

// The FSM `decl` of the instance keyed `prefix`, built from the run's
// variables; nothing where a signal it names was not found.
std::optional<FsmCount> FsmOf(const FsmDecl& decl, const std::string& prefix,
                              SimContext& ctx) {
  FsmCount fsm;
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
  fsm.legal = LegalStates(decl, prefix, ctx);
  return fsm;
}

// Arm the counting of the FSMs of the instance of `mod` keyed `prefix`.
void AttachInstance(const RtlirModule& mod, const std::string& prefix,
                    SimContext& ctx) {
  auto inst = std::make_shared<InstanceFsms>();
  inst->scope = CoverageScopeOfInstanceKey(prefix, ctx);
  std::int64_t legal = 0;
  for (const FsmDecl& decl : mod.fsms) {
    std::optional<FsmCount> fsm = FsmOf(decl, prefix, ctx);
    if (!fsm) continue;
    legal += static_cast<std::int64_t>(fsm->legal.size());
    inst->fsms.push_back(std::move(*fsm));
  }
  if (inst->fsms.empty()) return;
  CoverageControlState& cov = ctx.GetCoverageControlState();
  cov.SetCoverableItems(inst->scope, kCoverageTypeFsmState, legal);
  cov.SetAvailability(inst->scope, CoverageAvailability::kFull);
  cov.Control(CoverageControl::kStart, inst->scope, /*include_below=*/false);
  inst->resets = cov.ResetCount(inst->scope);
  for (const FsmCount& fsm : inst->fsms) {
    for (Variable* signal : fsm.signals) {
      signal->AddWatcher([inst, &cov]() {
        Count(*inst, cov);
        return false;
      });
    }
  }
  Count(*inst, cov);
}

}  // namespace

void AttachFsmCoverage(const RtlirDesign* design, SimContext& ctx) {
  if (design == nullptr) return;
  WalkInstancePaths(design,
                    [&ctx](const RtlirModule* mod, const std::string& prefix) {
                      if (!mod->fsms.empty()) AttachInstance(*mod, prefix, ctx);
                    });
}

}  // namespace delta
