#include "simulator/toggle_coverage.h"

#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/code_coverage.h"
#include "simulator/code_coverage_items.h"
#include "simulator/coverage_control.h"
#include "simulator/lowerer_child.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vpi_coverage.h"
#include "simulator/vpi_design_walk.h"

namespace delta {

namespace {

uint64_t WordMask(uint32_t width, std::size_t w) {
  const uint64_t kBits = width - (w * 64);
  return kBits >= 64 ? ~uint64_t{0} : (uint64_t{1} << kBits) - 1;
}

void ClearToggles(ToggleSignal& signal) {
  std::ranges::fill(signal.seen0, 0);
  std::ranges::fill(signal.seen1, 0);
  std::ranges::fill(signal.toggles, 0);
}

std::int64_t BothValues(const ToggleSignal& signal) {
  std::int64_t both = 0;
  for (std::size_t w = 0; w < signal.seen0.size(); ++w) {
    both += std::popcount(signal.seen0[w] & signal.seen1[w]);
  }
  return both;
}

void Observe(ToggleSignal& signal) {
  CoverageControlState& cov = *signal.coverage;
  CoverageInstanceItems<ToggleSignal>& inst = *signal.instance;
  ApplyCoverageResets(inst, kCoverageTypeToggle, cov, ClearToggles);
  const bool kCollecting = cov.IsCollecting(inst.scope, kCoverageTypeToggle);
  const Logic4Vec& value = signal.var->value;
  const std::size_t kWords =
      std::min<std::size_t>(value.nwords, signal.last.size());
  std::int64_t newly_covered = 0;
  for (std::size_t w = 0; w < kWords; ++w) {
    const Logic4Word kNow = value.words[w];
    const Logic4Word kBefore = signal.last[w];
    signal.last[w] = kNow;
    if (!kCollecting) continue;
    const uint64_t kKnown = ~kNow.bval & WordMask(value.width, w);
    uint64_t moved = kKnown & ~kBefore.bval & (kNow.aval ^ kBefore.aval);
    for (; moved != 0; moved &= moved - 1) {
      ++signal.toggles[(w * 64) + std::countr_zero(moved)];
    }
    const uint64_t kWasBoth = signal.seen0[w] & signal.seen1[w];
    signal.seen0[w] |= kKnown & ~kNow.aval;
    signal.seen1[w] |= kKnown & kNow.aval;
    newly_covered +=
        std::popcount(signal.seen0[w] & signal.seen1[w] & ~kWasBoth);
  }
  if (newly_covered == 0) return;
  inst.covered += newly_covered;
  cov.SetCoveredItems(inst.scope, kCoverageTypeToggle, inst.covered);
}

bool HasToggleBits(const Variable* var, SimContext& ctx) {
  if (var == nullptr || var->is_real || var->is_string || var->is_event ||
      var->is_virtual_interface || var->value.width == 0) {
    return false;
  }
  const DataType* type = var->declared_type;
  return type == nullptr || type->kind != DataTypeKind::kNamed ||
         ctx.FindClassType(type->type_name) == nullptr;
}

Variable* SignalNamed(const std::string& prefix, std::string_view name,
                      SimContext& ctx) {
  return ctx.FindVariable(VpiFlatName(prefix, name));
}

std::vector<Variable*> InstanceSignals(const RtlirModule& mod,
                                       const std::string& prefix,
                                       SimContext& ctx) {
  std::vector<Variable*> signals;
  std::unordered_set<Variable*> seen;
  auto add = [&](std::string_view name) {
    Variable* var = SignalNamed(prefix, name, ctx);
    if (HasToggleBits(var, ctx) && seen.insert(var).second) {
      signals.push_back(var);
    }
  };
  for (const RtlirPort& port : mod.ports) {
    if (port.num_unpacked_dims == 0) add(port.name);
  }
  for (const RtlirNet& net : mod.nets) add(net.name);
  for (const RtlirVariable& var : mod.variables) {
    if (!var.is_enum_constant && var.num_unpacked_dims == 0) add(var.name);
  }
  return signals;
}

ToggleSignal& AddSignal(Variable* var,
                        CoverageInstanceItems<ToggleSignal>& inst,
                        CoverageControlState& cov) {
  CodeCoverage& code = cov.Code();
  ToggleSignal& signal = code.toggle_signals.emplace_back();
  signal.var = var;
  signal.instance = &inst;
  signal.coverage = &cov;
  signal.seen0.assign(var->value.nwords, 0);
  signal.seen1.assign(var->value.nwords, 0);
  signal.last.assign(var->value.words, var->value.words + var->value.nwords);
  signal.toggles.assign(var->value.width, 0);
  auto [first, added] = code.toggles.try_emplace(var, &signal);
  if (added) {
    var->toggle = &signal;
  } else {
    signal.next = first->second->next;
    first->second->next = &signal;
  }
  inst.items.push_back(&signal);
  return signal;
}

}  // namespace

void ObserveToggle(ToggleSignal& signal) {
  for (ToggleSignal* each = &signal; each != nullptr; each = each->next) {
    Observe(*each);
  }
}

void AttachToggleCoverage(const RtlirDesign* design, SimContext& ctx) {
  CoverageControlState& cov = ctx.GetCoverageControlState();
  WalkInstancePaths(design, [&](const RtlirModule* mod,
                                const std::string& prefix) {
    const std::vector<Variable*> kSignals = InstanceSignals(*mod, prefix, ctx);
    if (kSignals.empty()) return;
    auto& inst = cov.Code().toggle_instances.emplace_back();
    inst.scope = CoverageScopeOfInstanceKey(prefix, ctx);
    std::int64_t bits = 0;
    for (Variable* var : kSignals) {
      AddSignal(var, inst, cov);
      bits += var->value.width;
    }
    ArmCoverageInstance(inst, kCoverageTypeToggle, bits, cov);
    for (ToggleSignal* signal : inst.items) {
      for (std::size_t w = 0; w < signal->last.size(); ++w) {
        signal->last[w].bval = ~uint64_t{0};
      }
      Observe(*signal);
    }
  });
}

EntityCoverage SignalToggleCoverage(const Variable* var,
                                    const std::string& scope,
                                    CoverageControlState& cov) {
  CodeCoverage& code = cov.Code();
  ToggleSignal* signal = code.toggles.at(var);
  for (ToggleSignal* each = signal; each != nullptr; each = each->next) {
    if (each->instance->scope == scope) signal = each;
  }
  ApplyCoverageResets(*signal->instance, kCoverageTypeToggle, cov,
                      ClearToggles);
  EntityCoverage bits;
  bits.total = signal->toggles.size();
  bits.covered = static_cast<std::uint64_t>(BothValues(*signal));
  for (std::uint64_t toggles : signal->toggles) bits.hit_count += toggles;
  return bits;
}

}  // namespace delta
