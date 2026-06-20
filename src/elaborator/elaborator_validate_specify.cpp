#include <algorithm>
#include <format>
#include <functional>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {

using PortMap = std::unordered_map<std::string_view, const PortDecl*>;
using SignalSet = std::unordered_set<std::string_view>;

// Validates a path terminal that resolves to a declared port `p`: checks the
// ref-port prohibition, direction compatibility, and (for sources) the net
// requirement. Emits at most one diagnostic.
void CheckPathTerminalPort(const PortDecl* p, const SpecifyTerminal& t,
                           SourceLoc loc, Direction allowed_dir,
                           std::string_view role, std::string_view dir_phrase,
                           bool require_net, DiagEngine& diag) {
  if (p->direction == Direction::kRef) {
    diag.Error(loc, std::format("ref port '{}' cannot be used as a "
                                "terminal in a specify block",
                                t.name));
    return;
  }
  if (p->direction != allowed_dir && p->direction != Direction::kInout) {
    diag.Error(loc, std::format("module path {} '{}' must be "
                                "connected to an {} port",
                                role, t.name, dir_phrase));
    return;
  }
  if (require_net) {
    bool is_var = !p->data_type.is_net && !p->data_type.is_interconnect;
    if (is_var) {
      diag.Error(loc,
                 std::format("module path source '{}' must be a net", t.name));
    }
  }
}

// Validates one terminal of a module path: it must name a port whose direction
// permits the given role (kInput for path sources, kOutput for destinations;
// inout is always allowed), it may not be a ref port, and a source must be a
// net. `role` is the word used in diagnostics ("source"/"destination").
void CheckSpecifyPathTerminal(const SpecifyTerminal& t, SourceLoc loc,
                              const PortMap& port_map,
                              const SignalSet& local_signals,
                              Direction allowed_dir, std::string_view role,
                              bool require_net, DiagEngine& diag) {
  std::string_view dir_phrase =
      allowed_dir == Direction::kInput ? "input or inout" : "output or inout";
  if (!t.interface_name.empty()) return;
  auto it = port_map.find(t.name);
  if (it != port_map.end()) {
    CheckPathTerminalPort(it->second, t, loc, allowed_dir, role, dir_phrase,
                          require_net, diag);
    return;
  }
  if (local_signals.contains(t.name)) {
    diag.Error(loc, std::format("module path {} '{}' is not connected "
                                "to an {} port",
                                role, t.name, dir_phrase));
  }
}

// Builds the port-name lookup for a module's declared ports.
PortMap BuildPortMap(const ModuleDecl* mod) {
  PortMap port_map;
  for (const auto& p : mod->ports) {
    if (!p.name.empty()) port_map[p.name] = &p;
  }
  return port_map;
}

// Collects net/var declarations that are local signals (not ports).
SignalSet BuildLocalSignals(const ModuleDecl* mod, const PortMap& port_map) {
  SignalSet local_signals;
  for (auto* mi : mod->items) {
    if ((mi->kind == ModuleItemKind::kNetDecl ||
         mi->kind == ModuleItemKind::kVarDecl) &&
        !mi->name.empty() && !port_map.contains(mi->name)) {
      local_signals.insert(mi->name);
    }
  }
  return local_signals;
}

// A timing-check terminal may not name a ref port.
void CheckTimingTerminal(const SpecifyTerminal& t, SourceLoc loc,
                         const PortMap& port_map, DiagEngine& diag) {
  if (!t.interface_name.empty()) return;
  auto it = port_map.find(t.name);
  if (it != port_map.end() && it->second->direction == Direction::kRef) {
    diag.Error(loc, std::format("ref port '{}' cannot be used as a "
                                "terminal in a specify block",
                                t.name));
  }
}

// Validates all source and destination terminals of one path declaration.
void CheckPathDeclTerminals(const SpecifyItem* si, const PortMap& port_map,
                            const SignalSet& local_signals, DiagEngine& diag) {
  for (const auto& t : si->path.src_ports) {
    CheckSpecifyPathTerminal(t, si->loc, port_map, local_signals,
                             Direction::kInput, "source",
                             /*require_net=*/true, diag);
  }
  for (const auto& t : si->path.dst_ports) {
    CheckSpecifyPathTerminal(t, si->loc, port_map, local_signals,
                             Direction::kOutput, "destination",
                             /*require_net=*/false, diag);
  }
}

// Validates the terminals of one specify item (path declaration or timing
// check); other item kinds are ignored.
void CheckSpecifyItemTerminals(const SpecifyItem* si, const PortMap& port_map,
                               const SignalSet& local_signals,
                               DiagEngine& diag) {
  if (si->kind == SpecifyItemKind::kPathDecl) {
    CheckPathDeclTerminals(si, port_map, local_signals, diag);
  } else if (si->kind == SpecifyItemKind::kTimingCheck) {
    CheckTimingTerminal(si->timing_check.ref_terminal, si->loc, port_map, diag);
    CheckTimingTerminal(si->timing_check.data_terminal, si->loc, port_map,
                        diag);
  }
}

// Pass: validate every path-source, path-destination, and timing-check terminal
// against the module's port directions.
void ValidatePathTerminals(const ModuleDecl* mod, const PortMap& port_map,
                           const SignalSet& local_signals, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      CheckSpecifyItemTerminals(si, port_map, local_signals, diag);
    }
  }
}

// Two path declarations have the same endpoints if their source and destination
// terminal lists name the same ports (and interfaces) in the same order.
bool SameEndpoints(const SpecifyPathDecl& a, const SpecifyPathDecl& b) {
  if (a.src_ports.size() != b.src_ports.size()) return false;
  if (a.dst_ports.size() != b.dst_ports.size()) return false;
  for (size_t i = 0; i < a.src_ports.size(); ++i) {
    if (a.src_ports[i].name != b.src_ports[i].name) return false;
    if (a.src_ports[i].interface_name != b.src_ports[i].interface_name)
      return false;
  }
  for (size_t i = 0; i < a.dst_ports.size(); ++i) {
    if (a.dst_ports[i].name != b.dst_ports[i].name) return false;
    if (a.dst_ports[i].interface_name != b.dst_ports[i].interface_name)
      return false;
  }
  return true;
}

// Reports if an ifnone path conflicts with an unconditional path on the same
// endpoints, or fails to match any companion state-dependent path.
void CheckIfnonePath(SpecifyItem* ifn,
                     const std::vector<SpecifyItem*>& unconditionals,
                     const std::vector<SpecifyItem*>& conditionals,
                     DiagEngine& diag) {
  for (auto* un : unconditionals) {
    if (SameEndpoints(ifn->path, un->path)) {
      diag.Error(ifn->loc,
                 "ifnone path conflicts with an unconditional "
                 "path on the same endpoints");
      break;
    }
  }
  if (conditionals.empty()) return;
  bool matched = false;
  for (auto* c : conditionals) {
    if (SameEndpoints(ifn->path, c->path)) {
      matched = true;
      break;
    }
  }
  if (!matched) {
    diag.Error(ifn->loc,
               "ifnone path endpoints do not match any companion "
               "state-dependent path");
  }
}

// Pass: ifnone path conflict / companion-match checks within each specify
// block.
void ValidateIfnonePaths(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    std::vector<SpecifyItem*> ifnones;
    std::vector<SpecifyItem*> conditionals;
    std::vector<SpecifyItem*> unconditionals;
    for (auto* si : item->specify_items) {
      if (si->kind != SpecifyItemKind::kPathDecl) continue;
      if (si->path.is_ifnone) {
        ifnones.push_back(si);
      } else if (si->path.condition != nullptr) {
        conditionals.push_back(si);
      } else {
        unconditionals.push_back(si);
      }
    }
    for (auto* ifn : ifnones) {
      CheckIfnonePath(ifn, unconditionals, conditionals, diag);
    }
  }
}

// Classifies how a port is referenced: 0 = entire port, 1 = bit-select,
// 2 = part-select (including indexed forms).
int RefCategory(const SpecifyTerminal& t) {
  switch (t.range_kind) {
    case SpecifyRangeKind::kNone:
      return 0;
    case SpecifyRangeKind::kBitSelect:
      return 1;
    default:
      return 2;
  }
}

// §30.4.4.3: two edge-sensitive paths to the same endpoints must reference
// every port the same way.
bool ConsistentRefs(const SpecifyPathDecl& a, const SpecifyPathDecl& b) {
  for (size_t i = 0; i < a.src_ports.size(); ++i) {
    if (RefCategory(a.src_ports[i]) != RefCategory(b.src_ports[i]))
      return false;
  }
  for (size_t i = 0; i < a.dst_ports.size(); ++i) {
    if (RefCategory(a.dst_ports[i]) != RefCategory(b.dst_ports[i]))
      return false;
  }
  return true;
}

// Collects the edge-sensitive path declarations within one specify block.
std::vector<SpecifyItem*> CollectEdgePaths(const ModuleItem* item) {
  std::vector<SpecifyItem*> edge_paths;
  for (auto* si : item->specify_items) {
    if (si->kind != SpecifyItemKind::kPathDecl) continue;
    if (si->path.edge == SpecifyEdge::kNone) continue;
    edge_paths.push_back(si);
  }
  return edge_paths;
}

// Reports if `edge_paths[cur]` references its ports differently from any
// preceding edge-sensitive path sharing the same endpoints (§30.4.4.3).
void CheckEdgePathConsistency(const std::vector<SpecifyItem*>& edge_paths,
                              size_t cur, DiagEngine& diag) {
  for (size_t i = 0; i < cur; ++i) {
    if (!SameEndpoints(edge_paths[i]->path, edge_paths[cur]->path)) continue;
    if (!ConsistentRefs(edge_paths[i]->path, edge_paths[cur]->path)) {
      diag.Error(edge_paths[cur]->loc,
                 "edge-sensitive paths to the same module path must "
                 "reference each port the same way (entire port, "
                 "bit-select, or part-select)");
      break;
    }
  }
}

// Pass: enforce consistent port-reference forms across edge-sensitive paths to
// the same module path (§30.4.4.3).
void ValidateEdgePathConsistency(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    std::vector<SpecifyItem*> edge_paths = CollectEdgePaths(item);
    for (size_t j = 0; j < edge_paths.size(); ++j) {
      CheckEdgePathConsistency(edge_paths, j, diag);
    }
  }
}

// Computes the bit-width of a single path terminal, or 0 if it cannot be
// determined statically.
uint32_t TerminalWidth(const SpecifyTerminal& t, const PortMap& port_map) {
  if (t.range_kind == SpecifyRangeKind::kBitSelect) return 1;
  if (t.range_kind == SpecifyRangeKind::kPartSelect) {
    auto l = ConstEvalInt(t.range_left);
    auto r = ConstEvalInt(t.range_right);
    if (!l || !r) return 0;
    auto hi = std::max(*l, *r);
    auto lo = std::min(*l, *r);
    return static_cast<uint32_t>(hi - lo + 1);
  }
  if (t.range_kind == SpecifyRangeKind::kPlusIndexed ||
      t.range_kind == SpecifyRangeKind::kMinusIndexed) {
    auto w = ConstEvalInt(t.range_right);
    if (!w || *w <= 0) return 0;
    return static_cast<uint32_t>(*w);
  }
  if (!t.interface_name.empty()) return 0;
  auto it = port_map.find(t.name);
  if (it == port_map.end()) return 0;
  return EvalTypeWidth(it->second->data_type);
}

// Sums the widths of a terminal list; sets `known` false if any width is
// unknown (and returns 0 in that case).
uint32_t SumWidths(const std::vector<SpecifyTerminal>& ts,
                   const PortMap& port_map, bool& known) {
  uint32_t total = 0;
  for (const auto& t : ts) {
    uint32_t w = TerminalWidth(t, port_map);
    if (w == 0) {
      known = false;
      return uint32_t{0};
    }
    total += w;
  }
  return total;
}

// Checks that one parallel module path has equal source and destination bit
// widths; non-parallel or data-source paths and unknown widths are skipped.
void CheckParallelPathWidth(const SpecifyItem* si, const PortMap& port_map,
                            DiagEngine& diag) {
  if (si->kind != SpecifyItemKind::kPathDecl) return;
  if (si->path.path_kind != SpecifyPathKind::kParallel) return;
  if (si->path.data_source != nullptr) return;
  bool src_known = true;
  bool dst_known = true;
  uint32_t src_bits = SumWidths(si->path.src_ports, port_map, src_known);
  uint32_t dst_bits = SumWidths(si->path.dst_ports, port_map, dst_known);
  if (src_known && dst_known && src_bits != dst_bits) {
    diag.Error(si->loc,
               "parallel path source and destination must have "
               "equal bit widths");
  }
}

// Pass: parallel module paths require equal source and destination bit widths.
void ValidateParallelPathWidths(const ModuleDecl* mod, const PortMap& port_map,
                                DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      CheckParallelPathWidth(si, port_map, diag);
    }
  }
}

// Reports every signal in `si->signal_list` that names a module-path
// destination in `path_dsts`, using `kw` as the declaration keyword.
void ReportPulseStyleConflicts(const SpecifyItem* si, const char* kw,
                               const SignalSet& path_dsts, DiagEngine& diag) {
  for (std::string_view sig : si->signal_list) {
    if (path_dsts.contains(sig)) {
      diag.Error(si->loc, std::format("{} declaration for '{}' conflicts "
                                      "with a module path that drives the "
                                      "same output",
                                      kw, sig));
    }
  }
}

// Updates the running set of module-path destinations from one specify item,
// then checks any pulsestyle/showcancelled declaration against that set.
void CheckPulseStyleItem(const SpecifyItem* si, SignalSet& path_dsts,
                         DiagEngine& diag) {
  if (si->kind == SpecifyItemKind::kPathDecl) {
    for (const auto& t : si->path.dst_ports) path_dsts.insert(t.name);
    return;
  }
  if (si->kind == SpecifyItemKind::kPulsestyle) {
    ReportPulseStyleConflicts(si, "pulsestyle", path_dsts, diag);
    return;
  }
  if (si->kind == SpecifyItemKind::kShowcancelled) {
    const char* kw =
        si->is_noshowcancelled ? "noshowcancelled" : "showcancelled";
    ReportPulseStyleConflicts(si, kw, path_dsts, diag);
  }
}

// Pass: pulsestyle/showcancelled declarations may not name an output already
// driven by a module path.
void ValidatePulseStyleConflicts(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    SignalSet path_dsts;
    for (auto* si : item->specify_items) {
      CheckPulseStyleItem(si, path_dsts, diag);
    }
  }
}

// Recursively verifies that every identifier operand in a path-delay expression
// names a specparam declared in the same specify block.
void CheckDelayExpr(const Expr* e, SourceLoc loc, const SignalSet& specparams,
                    DiagEngine& diag) {
  if (!e) return;
  switch (e->kind) {
    case ExprKind::kIdentifier:
      if (!specparams.contains(e->text)) {
        diag.Error(loc, std::format("module path delay operand '{}' is "
                                    "not a specparam",
                                    e->text));
      }
      return;
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary:
      CheckDelayExpr(e->lhs, loc, specparams, diag);
      return;
    case ExprKind::kBinary:
      CheckDelayExpr(e->lhs, loc, specparams, diag);
      CheckDelayExpr(e->rhs, loc, specparams, diag);
      return;
    case ExprKind::kTernary:
      CheckDelayExpr(e->condition, loc, specparams, diag);
      CheckDelayExpr(e->true_expr, loc, specparams, diag);
      CheckDelayExpr(e->false_expr, loc, specparams, diag);
      return;
    case ExprKind::kMinTypMax:
      CheckDelayExpr(e->lhs, loc, specparams, diag);
      CheckDelayExpr(e->condition, loc, specparams, diag);
      CheckDelayExpr(e->rhs, loc, specparams, diag);
      return;
    case ExprKind::kSelect:
      CheckDelayExpr(e->base, loc, specparams, diag);
      CheckDelayExpr(e->index, loc, specparams, diag);
      CheckDelayExpr(e->index_end, loc, specparams, diag);
      return;
    case ExprKind::kConcatenation:
    case ExprKind::kAssignmentPattern:
      for (auto* el : e->elements) CheckDelayExpr(el, loc, specparams, diag);
      return;
    case ExprKind::kReplicate:
      CheckDelayExpr(e->repeat_count, loc, specparams, diag);
      for (auto* el : e->elements) CheckDelayExpr(el, loc, specparams, diag);
      return;
    default:
      return;
  }
}

// Collects the names of all specparams declared in one specify block.
SignalSet CollectSpecparams(const ModuleItem* item) {
  SignalSet specparams;
  for (auto* si : item->specify_items) {
    if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
      specparams.insert(si->param_name);
    }
  }
  return specparams;
}

// Verifies that every delay-expression operand of one path declaration names a
// specparam; non-path items are ignored.
void CheckItemDelayOperands(const SpecifyItem* si, const SignalSet& specparams,
                            DiagEngine& diag) {
  if (si->kind != SpecifyItemKind::kPathDecl) return;
  for (auto* d : si->path.delays) CheckDelayExpr(d, si->loc, specparams, diag);
}

// Pass: every operand in a module-path delay expression must be a specparam.
void ValidateDelayOperands(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    SignalSet specparams = CollectSpecparams(item);
    for (auto* si : item->specify_items) {
      CheckItemDelayOperands(si, specparams, diag);
    }
  }
}

// Runs all specify-block validation passes for a single module/interface/
// program, in their original order.
void ValidateOneSpecifyModule(const ModuleDecl* mod, DiagEngine& diag) {
  PortMap port_map = BuildPortMap(mod);
  SignalSet local_signals = BuildLocalSignals(mod, port_map);

  ValidatePathTerminals(mod, port_map, local_signals, diag);
  ValidateIfnonePaths(mod, diag);
  ValidateEdgePathConsistency(mod, diag);
  ValidateParallelPathWidths(mod, port_map, diag);
  ValidatePulseStyleConflicts(mod, diag);
  ValidateDelayOperands(mod, diag);
}

}  // namespace

void Elaborator::ValidateSpecifyBlocks() {
  auto check_modules = [&](const std::vector<ModuleDecl*>& modules) {
    for (auto* mod : modules) ValidateOneSpecifyModule(mod, diag_);
  };
  check_modules(unit_->modules);
  check_modules(unit_->interfaces);
  check_modules(unit_->programs);
}

}  // namespace delta
