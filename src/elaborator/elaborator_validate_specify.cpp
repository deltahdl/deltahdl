#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_specify_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"

namespace delta {

void RegisterSpecifyBlockSpecparams(const ModuleItem* item, RtlirModule* mod,
                                    const TypedefMap& typedefs,
                                    SpecparamNameSets names, DiagEngine& diag) {
  std::unordered_set<std::string_view> in_block;
  for (const auto* sp : item->specify_items) {
    if (!sp || sp->kind != SpecifyItemKind::kSpecparam) continue;
    if (sp->is_pathpulse || sp->param_name.starts_with("PATHPULSE$")) continue;
    if (!in_block.insert(sp->param_name).second) {
      diag.Error(sp->loc,
                 std::format("redeclaration of specparam '{}' in the specify "
                             "block",
                             sp->param_name),
                 Subclause("3.13"));
    }
    names.specparams.insert(sp->param_name);
    names.constants.insert(sp->param_name);
    RtlirVariable var;
    var.name = sp->param_name;
    var.loc = sp->loc;
    DataType type;
    type.packed_dim_left = sp->param_packed_left;
    type.packed_dim_right = sp->param_packed_right;
    var.width = SpecparamWidth(type, sp->param_value, typedefs);
    var.is_real = SpecparamIsReal(type, sp->param_value);
    if (var.is_real) var.width = 64;
    var.init_expr = sp->param_value;
    mod->variables.push_back(var);
  }
}

namespace {

using IfaceMap = std::unordered_map<std::string_view, const ModuleDecl*>;

struct IfaceTerminal {
  bool is_interface = false;
  bool is_ref = false;
  Direction dir = Direction::kNone;
};

struct TerminalRole {
  Direction allowed_dir;
  std::string_view role;
  std::string_view dir_phrase;
  bool require_net;
};

TerminalRole SourceRole() {
  return {Direction::kInput, "source", "input or inout", true};
}
TerminalRole DestRole() {
  return {Direction::kOutput, "destination", "output or inout", false};
}

struct ModuleSignals {
  SignalSet local;
  SignalSet variable_ports;
  SignalSet local_nets;
};

struct SignalScope {
  const PortMap& port_map;
  const ModuleSignals& signals;
  const IfaceMap& iface_map;
};

IfaceTerminal ResolveIfaceTerminal(const SpecifyTerminal& t,
                                   const PortMap& port_map,
                                   const IfaceMap& iface_map) {
  IfaceTerminal r;
  if (t.interface_name.empty()) return r;
  auto pit = port_map.find(t.interface_name);
  if (pit == port_map.end()) return r;
  const PortDecl* p = pit->second;
  auto iit = iface_map.find(p->data_type.type_name);
  if (iit == iface_map.end()) return r;
  r.is_interface = true;
  std::string_view mp_name = p->data_type.modport_name;
  if (mp_name.empty()) return r;
  for (const auto* mp : iit->second->modports) {
    if (!mp || mp->name != mp_name) continue;
    for (const auto& member : mp->ports) {
      if (member.name != t.name) continue;
      r.dir = member.direction;
      r.is_ref = member.direction == Direction::kRef;
      return r;
    }
    break;
  }
  return r;
}

void CheckIfacePathTerminal(const IfaceTerminal& ift, const SpecifyTerminal& t,
                            SourceLoc loc, const TerminalRole& tr,
                            DiagEngine& diag) {
  if (ift.is_ref) {
    diag.Error(loc,
               std::format("ref modport member '{}.{}' cannot be used as "
                           "a terminal in a specify block",
                           t.interface_name, t.name),
               Subclause("25.6"));
    return;
  }
  if (ift.dir == Direction::kInput && tr.allowed_dir == Direction::kOutput) {
    diag.Error(loc,
               std::format("interface signal '{}.{}' is restricted by its "
                           "modport to an input and cannot be a module "
                           "path destination",
                           t.interface_name, t.name),
               Subclause("25.6"));
  } else if (ift.dir == Direction::kOutput &&
             tr.allowed_dir == Direction::kInput) {
    diag.Error(loc,
               std::format("interface signal '{}.{}' is restricted by its "
                           "modport to an output and cannot be a module "
                           "path source",
                           t.interface_name, t.name),
               Subclause("25.6"));
  }
}

bool CheckPathTerminalPort(const PortDecl* p, const SpecifyTerminal& t,
                           SourceLoc loc, const TerminalRole& tr,
                           DiagEngine& diag) {
  if (p->direction == Direction::kRef) {
    diag.Error(loc,
               std::format("ref port '{}' cannot be used as a "
                           "terminal in a specify block",
                           t.name),
               Subclause("25.6"));
    return true;
  }
  if (p->direction != tr.allowed_dir && p->direction != Direction::kInout) {
    diag.Error(loc,
               std::format("module path {} '{}' must be "
                           "connected to an {} port",
                           tr.role, t.name, tr.dir_phrase),
               Subclause("30.4.1"));
    return true;
  }
  return false;
}

bool PortIsVariable(const PortDecl& p, const ModuleSignals& signals) {
  if (p.data_type.kind == DataTypeKind::kImplicit && !p.has_explicit_var) {
    return signals.variable_ports.contains(p.name);
  }
  return !p.data_type.is_net;
}

void CheckSpecifyPathTerminal(const SpecifyTerminal& t, SourceLoc loc,
                              const SignalScope& scope, const TerminalRole& tr,
                              DiagEngine& diag) {
  if (!t.interface_name.empty()) {
    IfaceTerminal ift =
        ResolveIfaceTerminal(t, scope.port_map, scope.iface_map);
    if (ift.is_interface) CheckIfacePathTerminal(ift, t, loc, tr, diag);
    return;
  }
  auto it = scope.port_map.find(t.name);
  if (it != scope.port_map.end()) {
    if (CheckPathTerminalPort(it->second, t, loc, tr, diag)) return;
    if (tr.require_net && PortIsVariable(*it->second, scope.signals)) {
      diag.Error(loc,
                 std::format("module path source '{}' must be a net", t.name),
                 Subclause("30.4.1"));
    }
    return;
  }
  if (scope.signals.local.contains(t.name)) {
    diag.Error(loc,
               std::format("module path {} '{}' is not connected "
                           "to an {} port",
                           tr.role, t.name, tr.dir_phrase),
               Subclause("30.4.1"));
  }
}

PortMap BuildPortMap(const ModuleDecl* mod) {
  PortMap port_map;
  for (const auto& p : mod->ports) {
    if (!p.name.empty()) port_map[p.name] = &p;
  }
  return port_map;
}

ModuleSignals BuildLocalSignals(const ModuleDecl* mod,
                                const PortMap& port_map) {
  ModuleSignals signals;
  for (auto* mi : mod->items) {
    if ((mi->kind != ModuleItemKind::kNetDecl &&
         mi->kind != ModuleItemKind::kVarDecl) ||
        mi->name.empty()) {
      continue;
    }
    if (!port_map.contains(mi->name)) {
      signals.local.insert(mi->name);
      if (mi->kind == ModuleItemKind::kNetDecl) {
        signals.local_nets.insert(mi->name);
      }
    } else if (mi->kind == ModuleItemKind::kVarDecl) {
      signals.variable_ports.insert(mi->name);
    }
  }
  return signals;
}

void CheckTimingTerminal(const SpecifyTerminal& t, SourceLoc loc,
                         const SignalScope& scope, DiagEngine& diag) {
  const PortMap& port_map = scope.port_map;
  const IfaceMap& iface_map = scope.iface_map;
  if (!t.interface_name.empty()) {
    IfaceTerminal ift = ResolveIfaceTerminal(t, port_map, iface_map);
    if (ift.is_ref) {
      diag.Error(loc,
                 std::format("ref modport member '{}.{}' cannot be used "
                             "as a terminal in a specify block",
                             t.interface_name, t.name),
                 Subclause("25.6"));
    }
    return;
  }
  auto it = port_map.find(t.name);
  if (it != port_map.end() && it->second->direction == Direction::kRef) {
    diag.Error(loc,
               std::format("ref port '{}' cannot be used as a "
                           "terminal in a specify block",
                           t.name),
               Subclause("25.6"));
  }
  if (it == port_map.end() && scope.signals.local.contains(t.name)) {
    diag.Error(loc,
               std::format("timing check terminal '{}' is not a port of the "
                           "module",
                           t.name),
               Subclause("31.2"));
  }
}

void CheckTimingCheckNotifier(const SpecifyItem* si, const SignalScope& scope,
                              DiagEngine& diag) {
  std::string_view n = si->timing_check.notifier;
  if (n.empty()) return;
  auto it = scope.port_map.find(n);
  bool is_net = it != scope.port_map.end()
                    ? !PortIsVariable(*it->second, scope.signals)
                    : scope.signals.local_nets.contains(n);
  if (!is_net) return;
  diag.Error(
      si->loc,
      std::format("timing check notifier '{}' is a net, not a variable", n),
      Subclause("31.6"));
}

void CheckPathDeclTerminals(const SpecifyItem* si, const PortMap& port_map,
                            const ModuleSignals& signals,
                            const IfaceMap& iface_map, DiagEngine& diag) {
  SignalScope scope{port_map, signals, iface_map};
  for (const auto& t : si->path.src_ports) {
    CheckSpecifyPathTerminal(t, si->loc, scope, SourceRole(), diag);
  }
  for (const auto& t : si->path.dst_ports) {
    CheckSpecifyPathTerminal(t, si->loc, scope, DestRole(), diag);
  }
}

void CheckSpecifyItemTerminals(const SpecifyItem* si, const PortMap& port_map,
                               const ModuleSignals& signals,
                               const IfaceMap& iface_map, DiagEngine& diag) {
  if (si->kind == SpecifyItemKind::kPathDecl) {
    CheckPathDeclTerminals(si, port_map, signals, iface_map, diag);
  } else if (si->kind == SpecifyItemKind::kTimingCheck) {
    SignalScope scope{port_map, signals, iface_map};
    CheckTimingTerminal(si->timing_check.ref_terminal, si->loc, scope, diag);
    CheckTimingTerminal(si->timing_check.data_terminal, si->loc, scope, diag);
    CheckTimingCheckNotifier(si, scope, diag);
  }
}

void ValidatePathTerminals(const ModuleDecl* mod, const PortMap& port_map,
                           const ModuleSignals& signals,
                           const IfaceMap& iface_map, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      CheckSpecifyItemTerminals(si, port_map, signals, iface_map, diag);
    }
  }
}

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

std::vector<SpecifyItem*> ModuleSpecifyItems(const ModuleDecl* mod) {
  std::vector<SpecifyItem*> items;
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    items.insert(items.end(), item->specify_items.begin(),
                 item->specify_items.end());
  }
  return items;
}

bool IsSimplePath(const SpecifyPathDecl& path) {
  return path.edge == SpecifyEdge::kNone && path.data_source == nullptr;
}

void CheckIfnonePath(SpecifyItem* ifn,
                     const std::vector<SpecifyItem*>& unconditionals,
                     DiagEngine& diag) {
  for (auto* un : unconditionals) {
    if (SameEndpoints(ifn->path, un->path)) {
      diag.Error(ifn->loc,
                 "ifnone path conflicts with an unconditional "
                 "path on the same endpoints",
                 Subclause("30.4.4.4"));
      return;
    }
  }
}

void ValidateIfnonePaths(const ModuleDecl* mod, DiagEngine& diag) {
  std::vector<SpecifyItem*> ifnones;
  std::vector<SpecifyItem*> unconditionals;
  for (auto* si : ModuleSpecifyItems(mod)) {
    if (si->kind != SpecifyItemKind::kPathDecl) continue;
    if (si->path.is_ifnone) {
      ifnones.push_back(si);
    } else if (si->path.condition == nullptr && IsSimplePath(si->path)) {
      unconditionals.push_back(si);
    }
  }
  for (auto* ifn : ifnones) CheckIfnonePath(ifn, unconditionals, diag);
}

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

std::vector<SpecifyItem*> CollectEdgePaths(const ModuleDecl* mod) {
  std::vector<SpecifyItem*> edge_paths;
  for (auto* si : ModuleSpecifyItems(mod)) {
    if (si->kind != SpecifyItemKind::kPathDecl) continue;
    if (si->path.edge == SpecifyEdge::kNone) continue;
    edge_paths.push_back(si);
  }
  return edge_paths;
}

void CheckEdgePathConsistency(const std::vector<SpecifyItem*>& edge_paths,
                              size_t cur, DiagEngine& diag) {
  for (size_t i = 0; i < cur; ++i) {
    if (!SameEndpoints(edge_paths[i]->path, edge_paths[cur]->path)) continue;
    if (!ConsistentRefs(edge_paths[i]->path, edge_paths[cur]->path)) {
      diag.Error(edge_paths[cur]->loc,
                 "edge-sensitive paths to the same module path must "
                 "reference each port the same way (entire port, "
                 "bit-select, or part-select)",
                 Subclause("30.4.4.3"));
      break;
    }
  }
}

void ValidateEdgePathConsistency(const ModuleDecl* mod, DiagEngine& diag) {
  std::vector<SpecifyItem*> edge_paths = CollectEdgePaths(mod);
  for (size_t j = 0; j < edge_paths.size(); ++j) {
    CheckEdgePathConsistency(edge_paths, j, diag);
  }
}

bool SpecifyExprEqual(const Expr* a, const Expr* b);

bool SpecifySelectEqual(const Expr* a, const Expr* b) {
  return a->is_part_select_plus == b->is_part_select_plus &&
         a->is_part_select_minus == b->is_part_select_minus &&
         SpecifyExprEqual(a->base, b->base) &&
         SpecifyExprEqual(a->index, b->index) &&
         SpecifyExprEqual(a->index_end, b->index_end);
}

bool SpecifyElementListEqual(const Expr* a, const Expr* b) {
  if (!SpecifyExprEqual(a->repeat_count, b->repeat_count)) return false;
  if (a->elements.size() != b->elements.size()) return false;
  for (size_t i = 0; i < a->elements.size(); ++i)
    if (!SpecifyExprEqual(a->elements[i], b->elements[i])) return false;
  return true;
}

bool SpecifyExprEqual(const Expr* a, const Expr* b) {
  if (a == nullptr || b == nullptr) return a == b;
  if (a->kind != b->kind) return false;
  switch (a->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kTimeLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return a->int_val == b->int_val && a->text == b->text;
    case ExprKind::kRealLiteral:
      return a->real_val == b->real_val;
    case ExprKind::kStringLiteral:
      return a->text == b->text;
    case ExprKind::kIdentifier:
      return a->text == b->text && a->scope_prefix == b->scope_prefix;
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary:
      return a->op == b->op && SpecifyExprEqual(a->lhs, b->lhs);
    case ExprKind::kBinary:
      return a->op == b->op && SpecifyExprEqual(a->lhs, b->lhs) &&
             SpecifyExprEqual(a->rhs, b->rhs);
    case ExprKind::kTernary:
      return SpecifyExprEqual(a->condition, b->condition) &&
             SpecifyExprEqual(a->true_expr, b->true_expr) &&
             SpecifyExprEqual(a->false_expr, b->false_expr);
    case ExprKind::kSelect:
      return SpecifySelectEqual(a, b);
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
      return SpecifyElementListEqual(a, b);
    default:
      return false;
  }
}

bool SameTerminal(const SpecifyTerminal& a, const SpecifyTerminal& b) {
  return a.name == b.name && a.interface_name == b.interface_name &&
         a.range_kind == b.range_kind &&
         SpecifyExprEqual(a.range_left, b.range_left) &&
         SpecifyExprEqual(a.range_right, b.range_right);
}

bool SameTerminals(const std::vector<SpecifyTerminal>& a,
                   const std::vector<SpecifyTerminal>& b) {
  if (a.size() != b.size()) return false;
  for (size_t i = 0; i < a.size(); ++i)
    if (!SameTerminal(a[i], b[i])) return false;
  return true;
}

void CheckEdgePathUniqueness(const std::vector<SpecifyItem*>& edge_paths,
                             size_t cur, DiagEngine& diag) {
  const SpecifyPathDecl& c = edge_paths[cur]->path;
  if (c.condition == nullptr) return;
  for (size_t i = 0; i < cur; ++i) {
    const SpecifyPathDecl& p = edge_paths[i]->path;
    if (p.condition == nullptr) continue;
    if (p.edge != c.edge) continue;
    if (!SameTerminals(p.src_ports, c.src_ports)) continue;
    if (!SameTerminals(p.dst_ports, c.dst_ports)) continue;
    if (!SpecifyExprEqual(p.condition, c.condition)) continue;
    diag.Error(edge_paths[cur]->loc,
               "edge-sensitive state-dependent paths to the same module path "
               "must be made unique by edge, condition, or both",
               Subclause("30.4.4.3"));
    break;
  }
}

void ValidateEdgePathUniqueness(const ModuleDecl* mod, DiagEngine& diag) {
  std::vector<SpecifyItem*> edge_paths = CollectEdgePaths(mod);
  for (size_t j = 0; j < edge_paths.size(); ++j) {
    CheckEdgePathUniqueness(edge_paths, j, diag);
  }
}

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

void CheckEdgeParallelPathDestination(const SpecifyItem* si,
                                      const PortMap& port_map,
                                      DiagEngine& diag) {
  for (const auto& t : si->path.dst_ports) {
    std::string_view form;
    if (t.range_kind == SpecifyRangeKind::kNone) {
      if (TerminalWidth(t, port_map) > 1) form = "a vector";
    } else if (t.range_kind != SpecifyRangeKind::kBitSelect) {
      form = "a part-select";
    }
    if (form.empty()) continue;
    diag.Error(si->loc,
               std::format("destination '{}' of an edge-sensitive parallel "
                           "path is {}, where a scalar port or a bit-select "
                           "is required",
                           t.name, form),
               Subclause("30.4.3"));
  }
}

void CheckParallelPathWidth(const SpecifyItem* si, const PortMap& port_map,
                            DiagEngine& diag) {
  if (si->kind != SpecifyItemKind::kPathDecl) return;
  if (si->path.path_kind != SpecifyPathKind::kParallel) return;
  if (!IsSimplePath(si->path)) {
    CheckEdgeParallelPathDestination(si, port_map, diag);
    return;
  }
  bool src_known = true;
  bool dst_known = true;
  uint32_t src_bits = SumWidths(si->path.src_ports, port_map, src_known);
  uint32_t dst_bits = SumWidths(si->path.dst_ports, port_map, dst_known);
  if (src_known && dst_known && src_bits != dst_bits) {
    diag.Error(si->loc,
               "parallel path source and destination must have "
               "equal bit widths",
               Subclause("30.4.5"));
  }
}

void ValidateParallelPathWidths(const ModuleDecl* mod, const PortMap& port_map,
                                DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      CheckParallelPathWidth(si, port_map, diag);
    }
  }
}

void ReportPulseStyleConflicts(const SpecifyItem* si, const char* kw,
                               const SignalSet& path_dsts, DiagEngine& diag,
                               Subclause subclause) {
  for (const auto& out : si->path_outputs) {
    std::string_view sig = out.name;
    if (path_dsts.contains(sig)) {
      diag.Error(si->loc,
                 std::format("{} declaration for '{}' conflicts "
                             "with a module path that drives the "
                             "same output",
                             kw, sig),
                 subclause);
    }
  }
}

void CheckPulseStyleItem(const SpecifyItem* si, SignalSet& path_dsts,
                         DiagEngine& diag) {
  if (si->kind == SpecifyItemKind::kPathDecl) {
    for (const auto& t : si->path.dst_ports) path_dsts.insert(t.name);
    return;
  }
  if (si->kind == SpecifyItemKind::kPulsestyle) {
    ReportPulseStyleConflicts(si, "pulsestyle", path_dsts, diag,
                              Subclause("30.7.4.1"));
    return;
  }
  if (si->kind == SpecifyItemKind::kShowcancelled) {
    const char* kw =
        si->is_noshowcancelled ? "noshowcancelled" : "showcancelled";
    ReportPulseStyleConflicts(si, kw, path_dsts, diag, Subclause("30.7.4.2"));
  }
}

void ValidatePulseStyleConflicts(const ModuleDecl* mod, DiagEngine& diag) {
  SignalSet path_dsts;
  for (auto* si : ModuleSpecifyItems(mod)) {
    CheckPulseStyleItem(si, path_dsts, diag);
  }
}

void CheckItemDelayOperands(const SpecifyItem* si, const SignalSet& specparams,
                            DiagEngine& diag) {
  if (si->kind != SpecifyItemKind::kPathDecl) return;
  for (auto* d : si->path.delays) {
    CheckDelayExpr(d, si->loc, specparams, diag,
                   {"module path delay operand", Subclause("30.5")});
  }
}

void ValidateDelayOperands(const ModuleDecl* mod, DiagEngine& diag) {
  for (auto* item : mod->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    SignalSet specparams = CollectSpecparamsInScope(mod, item);
    for (auto* si : item->specify_items) {
      CheckItemDelayOperands(si, specparams, diag);
    }
  }
}

void ValidateOneSpecifyModule(const ModuleDecl* mod, const IfaceMap& iface_map,
                              DiagEngine& diag) {
  PortMap port_map = BuildPortMap(mod);
  ModuleSignals signals = BuildLocalSignals(mod, port_map);

  ValidatePathTerminals(mod, port_map, signals, iface_map, diag);
  ValidateIfnonePaths(mod, diag);
  ValidateEdgePathConsistency(mod, diag);
  ValidateEdgePathUniqueness(mod, diag);
  ValidateParallelPathWidths(mod, port_map, diag);
  ValidatePulseStyleConflicts(mod, diag);
  ValidateDelayOperands(mod, diag);
  ValidateTimingCheckLimitOperands(mod, diag);
  ValidateTimingCheckFlags(mod, diag);
  ValidateTimingCheckLimitNonNegative(mod, diag, TimingCheckKind::kSetup,
                                      "$setup", Subclause("31.3.1"));
  ValidateTimingCheckLimitNonNegative(mod, diag, TimingCheckKind::kHold,
                                      "$hold", Subclause("31.3.2"));
  ValidateTimingCheckLimitNonNegative(mod, diag, TimingCheckKind::kRemoval,
                                      "$removal", Subclause("31.3.4"));
  ValidateTimingCheckLimitNonNegative(mod, diag, TimingCheckKind::kRecovery,
                                      "$recovery", Subclause("31.3.5"));
  ValidateTimingCheckLimitNonNegative(mod, diag, TimingCheckKind::kSkew,
                                      "$skew", Subclause("31.4.1"));
  ValidateTimingCheckLimitNonNegative(mod, diag, TimingCheckKind::kTimeskew,
                                      "$timeskew", Subclause("31.4.2"));
  ValidateTimingCheckLimitNonNegative(mod, diag, TimingCheckKind::kFullskew,
                                      "$fullskew", Subclause("31.4.3"));
  ValidateTimingCheckLimitNonNegative(mod, diag, TimingCheckKind::kWidth,
                                      "$width", Subclause("31.4.4"));
  ValidateTimingCheckLimitNonNegative(mod, diag, TimingCheckKind::kPeriod,
                                      "$period", Subclause("31.4.5"));
  ValidateConditionExprs(mod, port_map, diag);
  ValidatePulseControlTerminals(mod, port_map, diag);
}

}  // namespace

void CheckDelayExpr(const Expr* e, SourceLoc loc, const SignalSet& specparams,
                    DiagEngine& diag, SpecifyConstantExpr constant_expr) {
  if (!e) return;
  switch (e->kind) {
    case ExprKind::kIdentifier:
      if (!specparams.contains(e->text)) {
        diag.Error(loc,
                   std::format("{} '{}' is not a specparam",
                               constant_expr.operand, e->text),
                   constant_expr.subclause);
      }
      return;
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary:
      CheckDelayExpr(e->lhs, loc, specparams, diag, constant_expr);
      return;
    case ExprKind::kBinary:
      CheckDelayExpr(e->lhs, loc, specparams, diag, constant_expr);
      CheckDelayExpr(e->rhs, loc, specparams, diag, constant_expr);
      return;
    case ExprKind::kTernary:
      CheckDelayExpr(e->condition, loc, specparams, diag, constant_expr);
      CheckDelayExpr(e->true_expr, loc, specparams, diag, constant_expr);
      CheckDelayExpr(e->false_expr, loc, specparams, diag, constant_expr);
      return;
    case ExprKind::kMinTypMax:
      CheckDelayExpr(e->lhs, loc, specparams, diag, constant_expr);
      CheckDelayExpr(e->condition, loc, specparams, diag, constant_expr);
      CheckDelayExpr(e->rhs, loc, specparams, diag, constant_expr);
      return;
    case ExprKind::kSelect:
      CheckDelayExpr(e->base, loc, specparams, diag, constant_expr);
      CheckDelayExpr(e->index, loc, specparams, diag, constant_expr);
      CheckDelayExpr(e->index_end, loc, specparams, diag, constant_expr);
      return;
    case ExprKind::kConcatenation:
    case ExprKind::kAssignmentPattern:
      for (auto* el : e->elements)
        CheckDelayExpr(el, loc, specparams, diag, constant_expr);
      return;
    case ExprKind::kReplicate:
      CheckDelayExpr(e->repeat_count, loc, specparams, diag, constant_expr);
      for (auto* el : e->elements)
        CheckDelayExpr(el, loc, specparams, diag, constant_expr);
      return;
    default:
      return;
  }
}

SignalSet CollectSpecparams(const ModuleItem* item) {
  SignalSet specparams;
  for (auto* si : item->specify_items) {
    if (si->kind == SpecifyItemKind::kSpecparam && !si->param_name.empty()) {
      specparams.insert(si->param_name);
    }
  }
  return specparams;
}

SignalSet CollectSpecparamsInScope(const ModuleDecl* mod,
                                   const ModuleItem* block) {
  SignalSet specparams = CollectSpecparams(block);
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kSpecparam && !item->name.empty()) {
      specparams.insert(item->name);
    }
  }
  return specparams;
}

void Elaborator::ValidateSpecifyBlocks() {
  IfaceMap iface_map;
  for (const auto* iface : unit_->interfaces) {
    if (iface && !iface->name.empty()) iface_map[iface->name] = iface;
  }
  auto check_modules = [&](const std::vector<ModuleDecl*>& modules) {
    for (auto* mod : modules) ValidateOneSpecifyModule(mod, iface_map, diag_);
  };
  check_modules(unit_->modules);
  check_modules(unit_->interfaces);
  check_modules(unit_->programs);
}

}  // namespace delta
