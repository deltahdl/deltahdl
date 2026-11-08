#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_internal.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"
#include "simulator/specify_timing_check.h"

namespace delta {

TerminalSelect SpecifyTerminalSelect(const SpecifyTerminal& t, SimContext& ctx,
                                     Arena& arena) {
  TerminalSelect sel;
  if (t.range_kind == SpecifyRangeKind::kNone || t.range_left == nullptr)
    return sel;
  sel.present = true;
  const int64_t kLeft = SelectBoundValue(EvalExpr(t.range_left, ctx, arena));
  sel.left = kLeft;
  sel.right = kLeft;
  if (t.range_kind == SpecifyRangeKind::kBitSelect || t.range_right == nullptr)
    return sel;
  const int64_t kRight = SelectBoundValue(EvalExpr(t.range_right, ctx, arena));
  sel.right = kRight;
  if (t.range_kind == SpecifyRangeKind::kPlusIndexed) {
    sel.left = kLeft + kRight - 1;
    sel.right = kLeft;
  } else if (t.range_kind == SpecifyRangeKind::kMinusIndexed) {
    sel.right = kLeft - kRight + 1;
  }
  return sel;
}

static std::string TerminalSelectText(const SpecifyTerminal& t, SimContext& ctx,
                                      Arena& arena) {
  const TerminalSelect kSel = SpecifyTerminalSelect(t, ctx, arena);
  if (!kSel.present) return {};
  if (t.range_kind == SpecifyRangeKind::kBitSelect || t.range_right == nullptr)
    return "[" + std::to_string(kSel.left) + "]";
  return "[" + std::to_string(kSel.left) + ":" + std::to_string(kSel.right) +
         "]";
}

std::string SpecifyTerminalName(const SpecifyTerminal& t) {
  if (t.interface_name.empty()) return std::string(t.name);
  std::string name(t.interface_name);
  name.append(".").append(t.name);
  return name;
}

static uint64_t PathDelayTicks(const Logic4Vec& value, const TimeScale& scale,
                               TimeUnit precision) {
  if (value.is_real) {
    const double kDelay = RealVecToDouble(value);
    return kDelay <= 0.0 ? 0u : RealDelayToTicks(kDelay, scale, precision);
  }
  const uint32_t kWidth = value.width == 0 ? 64u : value.width;
  const int64_t kSigned = SignExtend(value.ToUint64(), kWidth);
  return DelayToTicks(ClampPathDelay(kSigned), scale, precision);
}

PathDelay BuildPathDelayFromDecl(const SpecifyPathDecl& decl, SimContext& ctx,
                                 Arena& arena, std::size_t src_index,
                                 std::size_t dst_index) {
  PathDelay pd;
  if (src_index < decl.src_ports.size()) {
    pd.src_port = SpecifyTerminalName(decl.src_ports[src_index]);
    pd.src_select = TerminalSelectText(decl.src_ports[src_index], ctx, arena);
    pd.decl_src_port = SpecifyTerminalName(decl.src_ports.front());
  }
  if (dst_index < decl.dst_ports.size()) {
    pd.dst_port = SpecifyTerminalName(decl.dst_ports[dst_index]);
    pd.dst_select = TerminalSelectText(decl.dst_ports[dst_index], ctx, arena);
    pd.decl_dst_port = SpecifyTerminalName(decl.dst_ports.front());
  }
  pd.path_kind = decl.path_kind;
  pd.edge = decl.edge;
  pd.is_ifnone = decl.is_ifnone;
  pd.condition = SpecifyConditionText(decl.condition);
  pd.condition_expr = decl.condition;

  const TimeScale& scale = ActiveInstanceTimeScale(ctx);
  std::size_t count = decl.delays.size();
  if (count > 12) count = 12;
  pd.delay_count = static_cast<uint8_t>(count == 0 ? 1 : count);
  pd.source_delays.assign(decl.delays.begin(), decl.delays.end());
  pd.loc = decl.loc;
  pd.decl = &decl;
  pd.src_index = src_index;
  pd.dst_index = dst_index;

  for (std::size_t i = 0; i < count; ++i) {
    pd.delays[i] = PathDelayTicks(EvalExpr(decl.delays[i], ctx, arena), scale,
                                  ctx.GlobalPrecision());
  }

  ExpandTransitionDelays(pd);
  return pd;
}

template <typename Visit>
static void ForEachSpecifyItemOfKind(const std::vector<ModuleItem*>& blocks,
                                     SpecifyItemKind kind, const Visit& visit) {
  for (const auto* block : blocks) {
    if (block == nullptr) continue;
    for (const auto* si : block->specify_items) {
      if (si == nullptr || si->kind != kind) continue;
      visit(*si);
    }
  }
}

static void RegisterPathDelays(const std::vector<ModuleItem*>& blocks,
                               std::string_view inst_prefix, SimContext& ctx,
                               Arena& arena, SpecifyManager& mgr) {
  ForEachSpecifyItemOfKind(
      blocks, SpecifyItemKind::kPathDecl, [&](const SpecifyItem& si) {
        mgr.AddPathDelayFromDecl(si.path, ctx, arena, true, inst_prefix);
      });
}

static void RegisterTimingChecks(const std::vector<ModuleItem*>& blocks,
                                 std::string_view inst_prefix, SimContext& ctx,
                                 Arena& arena, SpecifyManager& mgr) {
  ForEachSpecifyItemOfKind(blocks, SpecifyItemKind::kTimingCheck,
                           [&](const SpecifyItem& si) {
                             mgr.AddTimingCheckUnderOptions(
                                 si.timing_check, ctx, arena, inst_prefix);
                           });
}

static void RegisterSpecparams(const std::vector<ModuleItem*>& blocks,
                               std::string_view inst_prefix, SimContext& ctx,
                               Arena& arena, SpecifyManager& mgr) {
  std::vector<std::string> names;
  ForEachSpecifyItemOfKind(blocks, SpecifyItemKind::kSpecparam,
                           [&](const SpecifyItem& si) {
                             if (si.param_name.empty()) return;
                             names.emplace_back(si.param_name);
                           });
  mgr.BindDesignSpecparams(std::move(names), ctx, arena, inst_prefix);
}

static void RegisterPulseStyles(const std::vector<ModuleItem*>& blocks,
                                std::string_view inst_prefix,
                                SpecifyManager& mgr) {
  ForEachSpecifyItemOfKind(
      blocks, SpecifyItemKind::kPulsestyle, [&](const SpecifyItem& si) {
        PulseStyle style =
            si.is_ondetect ? PulseStyle::kOnDetect : PulseStyle::kOnEvent;
        for (const auto& out : si.path_outputs) {
          std::string_view sig = out.name;
          mgr.SetPathOutputPulseStyle(
              std::string(inst_prefix) + std::string(sig), style);
        }
      });
}

static void RegisterShowCancelled(const std::vector<ModuleItem*>& blocks,
                                  std::string_view inst_prefix,
                                  SpecifyManager& mgr) {
  ForEachSpecifyItemOfKind(
      blocks, SpecifyItemKind::kShowcancelled, [&](const SpecifyItem& si) {
        ShowCancelled mode = si.is_noshowcancelled
                                 ? ShowCancelled::kNoshowcancelled
                                 : ShowCancelled::kShowcancelled;
        for (const auto& out : si.path_outputs) {
          std::string_view sig = out.name;
          mgr.SetPathOutputShowCancelled(
              std::string(inst_prefix) + std::string(sig), mode);
        }
      });
}

static void RegisterPathPulseSpecparams(const std::vector<ModuleItem*>& blocks,
                                        std::string_view inst_prefix,
                                        SimContext& ctx, Arena& arena,
                                        SpecifyManager& mgr) {
  std::vector<PulseControlSpecparam> specs;
  ForEachSpecifyItemOfKind(
      blocks, SpecifyItemKind::kSpecparam, [&](const SpecifyItem& si) {
        if (!si.is_pathpulse) return;
        PulseControlSpecparam s;
        s.inst_prefix = inst_prefix;
        s.input = si.pathpulse_input;
        s.output = si.pathpulse_output;
        s.reject = EvalExpr(si.pathpulse_reject, ctx, arena).ToUint64();
        s.has_error = si.pathpulse_error != nullptr;
        if (s.has_error) {
          s.error = EvalExpr(si.pathpulse_error, ctx, arena).ToUint64();
        }
        specs.push_back(s);
      });
  mgr.ResolvePulseControlSpecparams(specs);
}

void RegisterSpecifyBlocks(const std::vector<ModuleItem*>& blocks,
                           std::string_view inst_prefix, SimContext& ctx,
                           Arena& arena, SpecifyManager& mgr) {
  RegisterSpecparams(blocks, inst_prefix, ctx, arena, mgr);
  RegisterPathDelays(blocks, inst_prefix, ctx, arena, mgr);
  RegisterTimingChecks(blocks, inst_prefix, ctx, arena, mgr);
  RegisterPulseStyles(blocks, inst_prefix, mgr);
  RegisterShowCancelled(blocks, inst_prefix, mgr);
  RegisterPathPulseSpecparams(blocks, inst_prefix, ctx, arena, mgr);
}

void RegisterModuleGates(const ModuleGates& module,
                         std::string_view inst_prefix, SimContext& ctx,
                         Arena& arena, SpecifyManager& mgr) {
  for (const auto* gate : module.gates) {
    if (gate == nullptr) continue;
    mgr.AddPrimitiveDriversFromGate(*gate, ctx, arena, inst_prefix,
                                    &module.outputs);
  }
}

void RegisterModuleSpecparams(const std::vector<std::string_view>& names,
                              std::string_view inst_prefix, SimContext& ctx,
                              Arena& arena, SpecifyManager& mgr) {
  std::vector<std::string> bound;
  bound.reserve(names.size());
  for (std::string_view name : names) {
    if (name.empty()) continue;
    bound.emplace_back(name);
  }
  mgr.BindDesignSpecparams(std::move(bound), ctx, arena, inst_prefix);
}

}  // namespace delta
