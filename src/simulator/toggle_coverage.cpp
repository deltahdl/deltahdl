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
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vpi_coverage.h"
#include "simulator/vpi_design_walk.h"

namespace delta {

namespace {

// The bits of word `w` of a value `width` bits wide that are bits of it.
uint64_t WordMask(uint32_t width, std::size_t w) {
  const uint64_t kBits = width - (w * 64);
  return kBits >= 64 ? ~uint64_t{0} : (uint64_t{1} << kBits) - 1;
}

// §40.3.2.1 `SV_COV_RESET: a signal reset has seen neither value on any bit
// and toggled none, its current value standing as where it is now.
void ClearToggles(ToggleSignal& signal) {
  std::ranges::fill(signal.seen0, 0);
  std::ranges::fill(signal.seen1, 0);
  std::ranges::fill(signal.toggles, 0);
}

// The bits of `signal` that have held both values.
std::int64_t BothValues(const ToggleSignal& signal) {
  std::int64_t both = 0;
  for (std::size_t w = 0; w < signal.seen0.size(); ++w) {
    both += std::popcount(signal.seen0[w] & signal.seen1[w]);
  }
  return both;
}

// One look at the bits of `signal` for its instance: each known bit has held
// the value it holds now, and one that held the other known value at the last
// look has toggled; while the instance collects, that is counted, and a bit
// that now has held both is covered. An x or a z holds neither value.
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

// Whether `var` holds bits that toggle between 0 and 1: no real, string,
// event, class handle or virtual interface does.
bool HasToggleBits(const Variable* var, SimContext& ctx) {
  if (var == nullptr || var->is_real || var->is_string || var->is_event ||
      var->is_virtual_interface || var->value.width == 0 ||
      var->value.words == nullptr) {
    return false;
  }
  const DataType* type = var->declared_type;
  return type == nullptr || type->kind != DataTypeKind::kNamed ||
         ctx.FindClassType(type->type_name) == nullptr;
}

// The storage of the signal `name` of the instance keyed `prefix`; null where
// it has none to count, an unpacked aggregate's elements being kept apart.
Variable* SignalNamed(const std::string& prefix, std::string_view name,
                      SimContext& ctx) {
  const std::string kFlat = VpiFlatName(prefix, name);
  if (Variable* var = ctx.FindVariable(kFlat)) return var;
  Net* net = ctx.FindNet(kFlat);
  return net != nullptr ? net->resolved : nullptr;
}

// The signals of the instance of `mod` keyed `prefix` that hold toggling
// bits, each once.
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
  for (const RtlirNet& net : mod.nets) add(net.name);
  for (const RtlirVariable& var : mod.variables) {
    if (!var.is_enum_constant && var.num_unpacked_dims == 0 &&
        !var.is_dynamic && !var.is_queue) {
      add(var.name);
    }
  }
  return signals;
}

// The record of `var`'s bits for the instance `inst`, chained after the one
// another instance keeps of the same variable.
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
    ToggleSignal* tail = first->second;
    while (tail->next != nullptr) tail = tail->next;
    tail->next = &signal;
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
    // The value each holds as collection starts is one it has held.
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
  auto found = code.toggles.find(var);
  if (found == code.toggles.end()) return {};
  ToggleSignal* signal = found->second;
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
