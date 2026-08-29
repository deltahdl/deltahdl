#include <string>
#include <string_view>
#include <vector>

#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

namespace delta {

// Calls `visit` on every specify item of kind `kind` that `blocks` declares, in
// declaration order, skipping a null block or item. The four registration
// passes below walk the same items and differ only in what they do with one, so
// the walk is written once here.
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
        for (std::string_view sig : si.signal_list) {
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
        for (std::string_view sig : si.signal_list) {
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
  RegisterPathDelays(blocks, inst_prefix, ctx, arena, mgr);
  RegisterPulseStyles(blocks, inst_prefix, mgr);
  RegisterShowCancelled(blocks, inst_prefix, mgr);
  RegisterPathPulseSpecparams(blocks, inst_prefix, ctx, arena, mgr);
}

}  // namespace delta
