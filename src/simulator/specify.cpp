#include "simulator/specify.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/specify_internal.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/specify_timing_check.h"
#include "simulator/variable.h"

namespace delta {

uint64_t ClampPathDelay(int64_t signed_value) {
  return signed_value < 0 ? 0u : static_cast<uint64_t>(signed_value);
}

void ExpandTransitionDelays(PathDelay& pd) {
  switch (pd.delay_count) {
    case 1: {
      const uint64_t kT = pd.delays[0];
      for (int i = 1; i < 6; ++i) pd.delays[i] = kT;
      break;
    }
    case 2: {
      const uint64_t kTrise = pd.delays[0];
      const uint64_t kTfall = pd.delays[1];
      pd.delays[2] = kTrise;
      pd.delays[3] = kTrise;
      pd.delays[4] = kTfall;
      pd.delays[5] = kTfall;
      break;
    }
    case 3: {
      const uint64_t kTrise = pd.delays[0];
      const uint64_t kTfall = pd.delays[1];
      const uint64_t kTz = pd.delays[2];
      pd.delays[3] = kTrise;
      pd.delays[4] = kTz;
      pd.delays[5] = kTfall;
      break;
    }
    default:

      break;
  }

  if (pd.delay_count == 12) return;
  pd.delays[6] = std::min(pd.delays[2], pd.delays[0]);
  pd.delays[7] = std::max(pd.delays[3], pd.delays[0]);
  pd.delays[8] = std::min(pd.delays[4], pd.delays[1]);
  pd.delays[9] = std::max(pd.delays[5], pd.delays[1]);
  pd.delays[10] = std::max(pd.delays[4], pd.delays[2]);
  pd.delays[11] = std::min(pd.delays[3], pd.delays[5]);
}

static void AddSpecparamName(std::vector<std::string>& names,
                             std::string_view name) {
  if (name.empty()) return;
  for (const auto& seen : names) {
    if (seen == name) return;
  }
  names.emplace_back(name);
}

std::vector<std::string> CollectDeclaredSpecparams(const ModuleDecl& mod) {
  std::vector<std::string> names;
  for (const auto* item : mod.items) {
    if (item == nullptr) continue;
    if (item->kind == ModuleItemKind::kSpecparam) {
      AddSpecparamName(names, item->name);
      continue;
    }
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (const auto* si : item->specify_items) {
      if (si != nullptr && si->kind == SpecifyItemKind::kSpecparam)
        AddSpecparamName(names, si->param_name);
    }
  }
  return names;
}

bool ExprReadsSpecparam(const Expr* expr,
                        const std::vector<std::string>& specparams);

static bool AnyElementReadsSpecparam(
    const std::vector<Expr*>& elements,
    const std::vector<std::string>& specparams) {
  for (const auto* el : elements) {
    if (ExprReadsSpecparam(el, specparams)) return true;
  }
  return false;
}

bool ExprReadsSpecparam(const Expr* expr,
                        const std::vector<std::string>& specparams) {
  if (expr == nullptr) return false;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      for (const auto& name : specparams) {
        if (name == expr->text) return true;
      }
      return false;
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary:
      return ExprReadsSpecparam(expr->lhs, specparams);
    case ExprKind::kBinary:
      return ExprReadsSpecparam(expr->lhs, specparams) ||
             ExprReadsSpecparam(expr->rhs, specparams);
    case ExprKind::kTernary:
      return ExprReadsSpecparam(expr->condition, specparams) ||
             ExprReadsSpecparam(expr->true_expr, specparams) ||
             ExprReadsSpecparam(expr->false_expr, specparams);
    case ExprKind::kMinTypMax:
      return ExprReadsSpecparam(expr->lhs, specparams) ||
             ExprReadsSpecparam(expr->condition, specparams) ||
             ExprReadsSpecparam(expr->rhs, specparams);
    case ExprKind::kSelect:
      return ExprReadsSpecparam(expr->base, specparams) ||
             ExprReadsSpecparam(expr->index, specparams) ||
             ExprReadsSpecparam(expr->index_end, specparams);
    case ExprKind::kConcatenation:
    case ExprKind::kAssignmentPattern:
      return AnyElementReadsSpecparam(expr->elements, specparams);
    case ExprKind::kReplicate:
      return ExprReadsSpecparam(expr->repeat_count, specparams) ||
             AnyElementReadsSpecparam(expr->elements, specparams);
    default:
      return false;
  }
}

namespace {

std::size_t GateOutputTerminalCount(GateKind kind, std::size_t terminals) {
  switch (kind) {
    case GateKind::kBuf:
    case GateKind::kNot:
      return terminals == 0 ? 0 : terminals - 1;
    case GateKind::kPullup:
    case GateKind::kPulldown:
      return terminals;
    case GateKind::kTran:
    case GateKind::kRtran:
    case GateKind::kTranif0:
    case GateKind::kTranif1:
    case GateKind::kRtranif0:
    case GateKind::kRtranif1:
      return 0;
    default:
      return terminals == 0 ? 0 : 1;
  }
}

void FillPrimitiveDriverDelays(PrimitiveDriver& driver, const ModuleItem& gate,
                               SimContext& ctx, Arena& arena) {
  Expr* const kDelayExprs[3] = {gate.gate_delay, gate.gate_delay_fall,
                                gate.gate_delay_decay};
  PathDelay scratch;
  std::size_t count = 0;
  for (Expr* delay_expr : kDelayExprs) {
    if (delay_expr == nullptr) break;
    Logic4Vec value = EvalExpr(delay_expr, ctx, arena);
    const uint32_t kWidth = value.width == 0 ? 64u : value.width;
    const int64_t kSigned = SignExtend(value.ToUint64(), kWidth);
    scratch.delays[count] = ClampPathDelay(kSigned);
    ++count;
  }
  scratch.delay_count = static_cast<uint8_t>(count == 0 ? 1 : count);
  ExpandTransitionDelays(scratch);
  driver.delay_count = scratch.delay_count;
  for (int i = 0; i < 12; ++i) driver.delays[i] = scratch.delays[i];
}

}  // namespace

std::vector<PrimitiveDriver> BuildPrimitiveDriversFromGate(
    const ModuleItem& gate, SimContext& ctx, Arena& arena) {
  std::vector<PrimitiveDriver> drivers;
  const std::size_t kOutputs =
      GateOutputTerminalCount(gate.gate_kind, gate.gate_terminals.size());
  for (std::size_t i = 0; i < kOutputs; ++i) {
    const Expr* terminal = gate.gate_terminals[i];
    if (terminal == nullptr || terminal->kind != ExprKind::kIdentifier) {
      continue;
    }
    PrimitiveDriver driver;
    driver.output_port = std::string(terminal->text);
    FillPrimitiveDriverDelays(driver, gate, ctx, arena);
    drivers.push_back(std::move(driver));
  }
  return drivers;
}

static uint64_t GreatestAdmittedTransitionTime(
    const std::vector<PathCandidate>& candidates) {
  uint64_t max_time = 0;
  for (const auto& c : candidates) {
    if (c.path == nullptr || !c.condition_true) continue;
    if (c.last_transition_time > max_time) max_time = c.last_transition_time;
  }
  return max_time;
}

const PathDelay* SelectActivePath(const std::vector<PathCandidate>& candidates,
                                  uint8_t transition_slot) {
  if (candidates.empty()) return nullptr;

  uint64_t max_time = GreatestAdmittedTransitionTime(candidates);
  const PathDelay* best_path = nullptr;
  uint64_t best = 0;
  for (const auto& c : candidates) {
    if (c.path == nullptr) continue;
    if (!c.condition_true) continue;
    if (c.last_transition_time != max_time) continue;
    uint64_t d = c.path->delays[transition_slot];
    if (best_path == nullptr || d < best) {
      best = d;
      best_path = c.path;
    }
  }
  return best_path;
}

uint64_t SelectPathDelay(const std::vector<PathCandidate>& candidates,
                         uint8_t transition_slot) {
  const PathDelay* selected = SelectActivePath(candidates, transition_slot);
  return selected ? selected->delays[transition_slot] : 0;
}

bool StateDependentPathConditionEnables(Logic4Word condition_lsb) {
  const bool kUnknown = (condition_lsb.bval & 1u) != 0u;
  if (kUnknown) return true;
  return (condition_lsb.aval & 1u) != 0u;
}

void ReplacePathDelayRetaining(PathDelay& existing, PathDelay replacement,
                               const PathDelayRetention& retain) {
  const PathDelay kSaved = existing;
  existing = std::move(replacement);
  for (int i = 0; i < 12; ++i) {
    if (retain.delay[i]) existing.delays[i] = kSaved.delays[i];
    if (retain.reject[i]) existing.reject_limit[i] = kSaved.reject_limit[i];
    if (retain.error[i]) existing.error_limit[i] = kSaved.error_limit[i];
  }
  if (std::ranges::all_of(retain.reject, std::identity{})) {
    existing.reject_limit_source = kSaved.reject_limit_source;
  }
  if (std::ranges::all_of(retain.error, std::identity{})) {
    existing.error_limit_source = kSaved.error_limit_source;
  }
}

namespace {

bool UpdateNonconditionalPathDelays(std::vector<PathDelay>& path_delays,
                                    const PathDelay& delay,
                                    PathDelayRetention retain,
                                    bool match_inst_prefix) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.src_select == delay.src_select &&
        existing.dst_select == delay.dst_select &&
        (!match_inst_prefix || existing.inst_prefix == delay.inst_prefix)) {
      std::string saved_cond = existing.condition;
      bool saved_ifnone = existing.is_ifnone;
      ReplacePathDelayRetaining(existing, delay, retain);
      existing.condition = std::move(saved_cond);
      existing.is_ifnone = saved_ifnone;
      matched = true;
    }
  }
  return matched;
}

bool SdfEntryNamesPath(const PathDelay& existing, const PathDelay& entry) {
  return (entry.edge == SpecifyEdge::kNone || existing.edge == entry.edge) &&
         (entry.src_select.empty() ||
          existing.src_select == entry.src_select) &&
         (entry.dst_select.empty() || existing.dst_select == entry.dst_select);
}

bool ConditionalSdfEntryReaches(const PathDelay& existing,
                                const PathDelay& entry) {
  return existing.src_port == entry.src_port &&
         existing.dst_port == entry.dst_port &&
         existing.inst_prefix == entry.inst_prefix &&
         SpecifyConditionsMatch(existing.condition, entry.condition) &&
         existing.is_ifnone == entry.is_ifnone &&
         SdfEntryNamesPath(existing, entry);
}

void ReplaceWithSdfDelays(PathDelay& existing, PathDelay entry,
                          PathDelayRetention retain) {
  entry.path_kind = existing.path_kind;
  entry.edge = existing.edge;
  entry.src_select = existing.src_select;
  entry.dst_select = existing.dst_select;
  entry.condition = existing.condition;
  entry.condition_expr = existing.condition_expr;
  entry.is_ifnone = existing.is_ifnone;
  ReplacePathDelayRetaining(existing, std::move(entry), retain);
}

bool AnnotateNonconditionalSdfPaths(std::vector<PathDelay>& path_delays,
                                    const PathDelay& entry,
                                    PathDelayRetention retain) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == entry.src_port &&
        existing.dst_port == entry.dst_port &&
        existing.inst_prefix == entry.inst_prefix &&
        SdfEntryNamesPath(existing, entry)) {
      ReplaceWithSdfDelays(existing, entry, retain);
      matched = true;
    }
  }
  return matched;
}

}  // namespace

void SpecifyManager::AddPathDelay(PathDelay delay, bool preserve_pulse_limits) {
  const PathDelayRetention kRetain = PathDelayRetention::PulseLimits(
      preserve_pulse_limits, preserve_pulse_limits);
  const bool kIsNonconditional = delay.condition_expr == nullptr &&
                                 delay.condition.empty() && !delay.is_ifnone;
  if (kIsNonconditional) {
    if (!UpdateNonconditionalPathDelays(path_delays_, delay, kRetain, true)) {
      path_delays_.push_back(std::move(delay));
    }
    return;
  }
  for (auto& existing : path_delays_) {
    if (existing.src_port == delay.src_port &&
        existing.dst_port == delay.dst_port &&
        existing.src_select == delay.src_select &&
        existing.dst_select == delay.dst_select &&
        existing.inst_prefix == delay.inst_prefix &&
        SpecifyConditionsMatch(existing.condition, delay.condition) &&
        existing.condition_expr == delay.condition_expr &&
        existing.is_ifnone == delay.is_ifnone) {
      ReplacePathDelayRetaining(existing, std::move(delay), kRetain);
      return;
    }
  }
  path_delays_.push_back(std::move(delay));
}

bool SpecifyManager::AnnotateSdfPathDelay(const PathDelay& delay,
                                          PathDelayRetention retain) {
  const bool kSdfIsNonconditional = delay.condition.empty() && !delay.is_ifnone;
  if (kSdfIsNonconditional) {
    return AnnotateNonconditionalSdfPaths(path_delays_, delay, retain);
  }
  bool matched = false;
  for (auto& existing : path_delays_) {
    if (!ConditionalSdfEntryReaches(existing, delay)) continue;
    ReplaceWithSdfDelays(existing, delay, retain);
    matched = true;
  }
  return matched;
}

namespace {

void AddPathDelayValues(PathDelay& existing,
                        const SdfPathDelayIncrement& deltas) {
  for (int i = 0; i < 12; ++i) {
    existing.delays[i] =
        ClampPathDelay(static_cast<int64_t>(existing.delays[i]) + deltas[i]);
  }
}

bool IncrementNonconditionalPathDelays(std::vector<PathDelay>& path_delays,
                                       const PathDelay& delta,
                                       const SdfPathDelayIncrement& deltas) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port &&
        existing.inst_prefix == delta.inst_prefix &&
        SdfEntryNamesPath(existing, delta)) {
      AddPathDelayValues(existing, deltas);
      matched = true;
    }
  }
  return matched;
}

bool IncrementConditionalPathDelays(std::vector<PathDelay>& path_delays,
                                    const PathDelay& delta,
                                    const SdfPathDelayIncrement& deltas) {
  bool matched = false;
  for (auto& existing : path_delays) {
    if (!ConditionalSdfEntryReaches(existing, delta)) continue;
    AddPathDelayValues(existing, deltas);
    matched = true;
  }
  return matched;
}

}  // namespace

bool SpecifyManager::IncrementSdfPathDelay(
    const PathDelay& delta, const SdfPathDelayIncrement& deltas) {
  const bool kSdfIsNonconditional = delta.condition.empty() && !delta.is_ifnone;
  if (kSdfIsNonconditional) {
    return IncrementNonconditionalPathDelays(path_delays_, delta, deltas);
  }
  return IncrementConditionalPathDelays(path_delays_, delta, deltas);
}

namespace {

void AddInterconnectDelayValues(InterconnectDelay& existing,
                                const InterconnectDelay& delta) {
  existing.rise += delta.rise;
  existing.fall += delta.fall;
  for (int i = 0; i < 12; ++i) {
    existing.delays[i] += delta.delays[i];
    existing.reject_limit[i] += delta.reject_limit[i];
    existing.error_limit[i] += delta.error_limit[i];
  }
}

const InterconnectDelay* FindAllSourceInterconnectDelay(
    const std::vector<InterconnectDelay>& delays, const std::string& load) {
  for (const auto& delay : delays) {
    if (delay.dst_port == load && delay.covered_sources.empty()) return &delay;
  }
  return nullptr;
}

void IncrementInterconnectDelayFromSource(
    std::vector<InterconnectDelay>& delays, const InterconnectDelay& delta) {
  for (auto& existing : delays) {
    if (existing.src_port == delta.src_port &&
        existing.dst_port == delta.dst_port) {
      AddInterconnectDelayValues(existing, delta);
      return;
    }
  }
  InterconnectDelay seeded = delta;
  if (const auto* base =
          FindAllSourceInterconnectDelay(delays, delta.dst_port)) {
    seeded = *base;
    seeded.src_port = delta.src_port;
    seeded.covered_sources = delta.covered_sources;
    AddInterconnectDelayValues(seeded, delta);
  }
  delays.push_back(std::move(seeded));
}

void IncrementInterconnectDelayFromAllSources(
    std::vector<InterconnectDelay>& delays, const InterconnectDelay& delta) {
  bool has_all_sources = false;
  for (auto& existing : delays) {
    if (existing.dst_port != delta.dst_port) continue;
    AddInterconnectDelayValues(existing, delta);
    if (existing.covered_sources.empty()) has_all_sources = true;
  }
  if (!has_all_sources) delays.push_back(delta);
}

}  // namespace

void SpecifyManager::IncrementInterconnectDelay(
    const InterconnectDelay& delta) {
  if (delta.covered_sources.empty()) {
    IncrementInterconnectDelayFromAllSources(interconnect_delays_, delta);
    return;
  }
  IncrementInterconnectDelayFromSource(interconnect_delays_, delta);
}

void SpecifyManager::AddTimingCheck(TimingCheckEntry check) {
  if (check.decl != nullptr) {
    for (auto& existing : timing_checks_) {
      if (existing.decl == check.decl &&
          existing.inst_prefix == check.inst_prefix) {
        existing = std::move(check);
        return;
      }
    }
    timing_checks_.push_back(std::move(check));
    return;
  }
  for (auto& existing : timing_checks_) {
    if (existing.inst_prefix == check.inst_prefix &&
        existing.kind == check.kind &&
        existing.ref_signal == check.ref_signal &&
        existing.ref_select == check.ref_select &&
        existing.ref_edge == check.ref_edge &&
        existing.data_signal == check.data_signal &&
        existing.data_select == check.data_select &&
        existing.data_edge == check.data_edge &&
        SpecifyConditionsMatch(existing.condition, check.condition)) {
      existing = std::move(check);
      return;
    }
  }
  timing_checks_.push_back(std::move(check));
}

void SpecifyManager::AddPrimitiveDriver(PrimitiveDriver driver) {
  primitive_drivers_.push_back(std::move(driver));
}

void SpecifyManager::AddPrimitiveDriversFromGate(
    const ModuleItem& gate, SimContext& ctx, Arena& arena,
    std::string_view inst_prefix,
    const std::vector<std::string_view>* module_outputs) {
  for (auto& driver : BuildPrimitiveDriversFromGate(gate, ctx, arena)) {
    driver.inst_prefix = inst_prefix;
    if (module_outputs != nullptr) {
      driver.drives_module_output =
          std::ranges::find(*module_outputs, driver.output_port) !=
          module_outputs->end();
    }
    AddPrimitiveDriver(std::move(driver));
  }
  for (const auto& seen : gate_decls_) {
    if (seen.gate == &gate && seen.inst_prefix == inst_prefix) return;
  }
  gate_decls_.push_back({&gate, std::string(inst_prefix)});
}

void SpecifyManager::AddPathDelayFromDecl(const SpecifyPathDecl& decl,
                                          SimContext& ctx, Arena& arena,
                                          bool default_pulse_limits,
                                          std::string_view inst_prefix) {
  const bool kFull = decl.path_kind == SpecifyPathKind::kFull;
  const std::size_t kSources =
      kFull ? std::max<std::size_t>(decl.src_ports.size(), 1) : 1;
  const std::size_t kDestinations =
      kFull ? std::max<std::size_t>(decl.dst_ports.size(), 1) : 1;
  for (std::size_t src = 0; src < kSources; ++src) {
    for (std::size_t dst = 0; dst < kDestinations; ++dst) {
      PathDelay pd = BuildPathDelayFromDecl(decl, ctx, arena, src, dst);
      pd.inst_prefix = inst_prefix;
      if (default_pulse_limits) {
        InitDefaultPulseLimits(pd);
        ApplyGlobalPulseLimits(pd, reject_pulse_pct_, error_pulse_pct_);
      }
      path_decls_.push_back(
          {&decl, std::string(inst_prefix), path_delays_.size(), src, dst});
      path_delays_.push_back(std::move(pd));
    }
  }
}

void SpecifyManager::BindDesignSpecparams(std::vector<std::string> names,
                                          SimContext& ctx, Arena& arena,
                                          std::string_view inst_prefix) {
  for (auto& name : names) {
    if (IsDeclaredSpecparam(inst_prefix, name)) continue;
    declared_specparams_.push_back({std::string(inst_prefix), std::move(name)});
  }
  specparam_ctx_ = &ctx;
  specparam_arena_ = &arena;
}

void SpecifyManager::RecordSpecparamInitializer(std::string_view inst_prefix,
                                                std::string_view name,
                                                const Expr* init) {
  for (auto& declared : declared_specparams_) {
    if (declared.inst_prefix == inst_prefix && declared.name == name) {
      declared.init = init;
    }
  }
}

bool SpecifyManager::IsDeclaredSpecparam(std::string_view inst_prefix,
                                         std::string_view name) const {
  for (const auto& declared : declared_specparams_) {
    if (declared.inst_prefix == inst_prefix && declared.name == name) {
      return true;
    }
  }
  return false;
}

}  // namespace delta
