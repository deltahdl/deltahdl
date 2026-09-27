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

namespace delta {

// §32.4.1 (printed page 925): the select the specify path terminal `t` was
// written with, spelled as PathDelay::src_select describes; empty for a whole
// port. An indexed part-select, `a[i +: 2]`, is spelled as the part it covers.
static std::string TerminalSelectText(const SpecifyTerminal& t, SimContext& ctx,
                                      Arena& arena) {
  if (t.range_kind == SpecifyRangeKind::kNone || t.range_left == nullptr)
    return {};
  const int64_t kLeft = SelectBoundValue(EvalExpr(t.range_left, ctx, arena));
  if (t.range_kind == SpecifyRangeKind::kBitSelect || t.range_right == nullptr)
    return "[" + std::to_string(kLeft) + "]";
  const int64_t kRight = SelectBoundValue(EvalExpr(t.range_right, ctx, arena));
  int64_t msb = kLeft;
  int64_t lsb = kRight;
  if (t.range_kind == SpecifyRangeKind::kPlusIndexed) {
    msb = kLeft + kRight - 1;
    lsb = kLeft;
  } else if (t.range_kind == SpecifyRangeKind::kMinusIndexed) {
    lsb = kLeft - kRight + 1;
  }
  return "[" + std::to_string(msb) + ":" + std::to_string(lsb) + "]";
}

// §30.4.2 (printed page 873): a path terminal is a port_identifier or
// `interface_identifier . port_identifier`, and the second names the signal of
// the module's interface port by both names, as the module's own text reads it
// (`p.a`). Kept as the port name alone, a path from `p.a` started at an `a`
// nothing in the module reads, so no transition was ever timed through it.
static std::string TerminalName(const SpecifyTerminal& t) {
  if (t.interface_name.empty()) return std::string(t.name);
  std::string name(t.interface_name);
  name.append(".").append(t.name);
  return name;
}

// §22.7 (printed page 716): "The time unit is the unit of measurement for time
// values such as the simulation time and delay values", so a path delay is a
// count of the declaring module's time unit, and a real one, `specparam tr =
// 2.5`, keeps what of its fraction the module's precision holds (§3.14.1). The
// path's slots are counted in ticks of the design's global precision, which
// §32.4.1's SDF values are scaled into as well.
static uint64_t PathDelayTicks(const Logic4Vec& value, const TimeScale& scale,
                               TimeUnit precision) {
  if (value.is_real) {
    const double kDelay = RealVecToDouble(value);
    // §30.5.1: a delay expression that evaluates negative is treated as zero.
    return kDelay <= 0.0 ? 0u : RealDelayToTicks(kDelay, scale, precision);
  }
  const uint32_t kWidth = value.width == 0 ? 64u : value.width;
  const int64_t kSigned = SignExtend(value.ToUint64(), kWidth);
  return DelayToTicks(ClampPathDelay(kSigned), scale, precision);
}

PathDelay BuildPathDelayFromDecl(const SpecifyPathDecl& decl, SimContext& ctx,
                                 Arena& arena) {
  PathDelay pd;
  if (!decl.src_ports.empty()) {
    pd.src_port = TerminalName(decl.src_ports.front());
    pd.src_select = TerminalSelectText(decl.src_ports.front(), ctx, arena);
  }
  if (!decl.dst_ports.empty()) {
    pd.dst_port = TerminalName(decl.dst_ports.front());
    pd.dst_select = TerminalSelectText(decl.dst_ports.front(), ctx, arena);
  }
  pd.path_kind = decl.path_kind;
  pd.edge = decl.edge;
  pd.is_ifnone = decl.is_ifnone;
  pd.condition = SpecifyConditionText(decl.condition);
  // §30.4.4: SelectModulePathDelay in simulator/module_path_delay.cpp evaluates
  // this condition for §30.5.3's activity test, which the text above cannot
  // answer, being rendered for §32.4.1's SDF COND matching.
  pd.condition_expr = decl.condition;

  // The parser accepts only the one/two/three/six/twelve delay lists of
  // Syntax 30-6 (§30.5); an empty list defaults to a single typical delay.
  const TimeScale& kScale = ActiveInstanceTimeScale(ctx);
  std::size_t count = decl.delays.size();
  if (count > 12) count = 12;
  pd.delay_count = static_cast<uint8_t>(count == 0 ? 1 : count);

  for (std::size_t i = 0; i < count; ++i) {
    // §30.5.1: a single value is the typical delay; a colon-separated
    // min:typ:max triple selects one member. EvalExpr resolves a
    // constant_mintypmax_expression against the context's delay mode.
    pd.delays[i] = PathDelayTicks(EvalExpr(decl.delays[i], ctx, arena), kScale,
                                  ctx.GlobalPrecision());
  }

  // §30.5.1 / Table 30-2: distribute the listed delays over the twelve
  // transition slots according to how many were specified.
  ExpandTransitionDelays(pd);
  return pd;
}

// Calls `visit` on every specify item of kind `kind` that `blocks` declares, in
// declaration order, skipping a null block or item. The six registration passes
// below walk the same items and differ only in what they do with one, so the
// walk is written once here.
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

// §30.4: the module path delays, one per path_declaration. Each path is given
// the §30.7 default pulse limits, which is the state the PATHPULSE$ specparams
// resolved afterwards replace.
static void RegisterPathDelays(const std::vector<ModuleItem*>& blocks,
                               std::string_view inst_prefix, SimContext& ctx,
                               Arena& arena, SpecifyManager& mgr) {
  ForEachSpecifyItemOfKind(
      blocks, SpecifyItemKind::kPathDecl, [&](const SpecifyItem& si) {
        mgr.AddPathDelayFromDecl(si.path, ctx, arena,
                                 /*default_pulse_limits=*/true, inst_prefix);
      });
}

// §31.2: the system_timing_check declarations of Syntax 30-1, each built under
// the invocation options §31.9.4 gives the manager and filed as a
// TimingCheckEntry so §32.4.2's SDF TIMINGCHECK annotation has a declared check
// to land on.
//
// The check is registered under `inst_prefix` because §31.3 has it name its
// reference and data signals by the declaring module's own port names, so two
// instances of one cell declare checks spelled identically and would otherwise
// be filed as one. The prefix is also what
// SpecifyManager::RebuildTimingChecksForSpecparam evaluates a constraint limit
// under when §32.4.3's LABEL annotation reprices a specparam that limit reads.
static void RegisterTimingChecks(const std::vector<ModuleItem*>& blocks,
                                 std::string_view inst_prefix, SimContext& ctx,
                                 Arena& arena, SpecifyManager& mgr) {
  ForEachSpecifyItemOfKind(blocks, SpecifyItemKind::kTimingCheck,
                           [&](const SpecifyItem& si) {
                             mgr.AddTimingCheckUnderOptions(
                                 si.timing_check, ctx, arena, inst_prefix);
                           });
}

// §30.3: the specparam_declarations of Syntax 30-1, bound to `mgr` so §32.4.3's
// LABEL annotation can reach them. Binding is also what gives the manager the
// context and arena a LABEL writes an annotated value into, so this runs for a
// specify block that declares no specparam at all.
//
// The names are bound under `inst_prefix` because §30.3 has the declaration
// name the specparam by a bare name, while Lowerer::CreateChildModuleVariables
// keys an instantiated module's specparam under its instance prefix.
//
// Only the specparams declared inside a specify block are collected, `blocks`
// being all this is given. §6.20.5's other declaration site, the module body
// outside every specify block, is bound by RegisterModuleSpecparams below,
// which reads the names off RtlirModule::specparam_names.
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

// §30.7.4.1: the pulsestyle_onevent and pulsestyle_ondetect declarations of
// Syntax 30-8, each selecting the pulse filtering style for every path output
// it names.
// The output is qualified with `inst_prefix` because §30.4 has the
// declaration name a port of the module it stands in by its bare name, so two
// instances of one cell name the same output and would otherwise share one
// style.
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

// §30.7.4.2: the showcancelled and noshowcancelled declarations of
// Syntax 30-9, each selecting the negative-pulse mode for every path output it
// names.
// The output is qualified with `inst_prefix` for the same reason
// RegisterPulseStyles qualifies it: a bare port name is shared by every
// instance of the cell declaring the specify block.
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

// §30.7.1: the PATHPULSE$ specparams of Syntax 30-7, collected across every
// block and resolved onto `mgr` in one call. Collecting first is what lets a
// path-specific PATHPULSE$ specparam take precedence over a nonpath-specific
// one whichever order the two were declared in. A specparam that states only a
// reject limit leaves `has_error` clear, and §30.7.1 makes that reject limit
// serve as the error limit too.
// `specs` holds the specparams of this one scope, and they are resolved onto
// `mgr` in one call, so a nonpath-specific PATHPULSE$ specparam reaches the
// module paths of the instance that declared it and no others.
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

void RegisterModuleGates(const std::vector<ModuleItem*>& gates,
                         std::string_view inst_prefix, SimContext& ctx,
                         Arena& arena, SpecifyManager& mgr) {
  for (const auto* gate : gates) {
    if (gate == nullptr) continue;
    mgr.AddPrimitiveDriversFromGate(*gate, ctx, arena, inst_prefix);
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
