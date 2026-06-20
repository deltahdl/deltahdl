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

// Validates one terminal of a module path: it must name a port whose direction
// permits the given role (kInput for path sources, kOutput for destinations;
// inout is always allowed), it may not be a ref port, and a source must be a
// net. `role` is the word used in diagnostics ("source"/"destination").
static void CheckSpecifyPathTerminal(
    const SpecifyTerminal& t, SourceLoc loc,
    const std::unordered_map<std::string_view, const PortDecl*>& port_map,
    const std::unordered_set<std::string_view>& local_signals,
    Direction allowed_dir, std::string_view role, bool require_net,
    DiagEngine& diag) {
  std::string_view dir_phrase =
      allowed_dir == Direction::kInput ? "input or inout" : "output or inout";
  if (!t.interface_name.empty()) return;
  auto it = port_map.find(t.name);
  if (it != port_map.end()) {
    const PortDecl* p = it->second;
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
        diag.Error(
            loc, std::format("module path source '{}' must be a net", t.name));
      }
    }
    return;
  }
  if (local_signals.contains(t.name)) {
    diag.Error(loc, std::format("module path {} '{}' is not connected "
                                "to an {} port",
                                role, t.name, dir_phrase));
  }
}

void Elaborator::ValidateSpecifyBlocks() {
  auto check_modules = [&](const std::vector<ModuleDecl*>& modules) {
    for (auto* mod : modules) {
      std::unordered_map<std::string_view, const PortDecl*> port_map;
      for (const auto& p : mod->ports) {
        if (!p.name.empty()) port_map[p.name] = &p;
      }

      std::unordered_set<std::string_view> local_signals;
      for (auto* mi : mod->items) {
        if ((mi->kind == ModuleItemKind::kNetDecl ||
             mi->kind == ModuleItemKind::kVarDecl) &&
            !mi->name.empty() && !port_map.contains(mi->name)) {
          local_signals.insert(mi->name);
        }
      }

      auto check_source = [&](const SpecifyTerminal& t, SourceLoc loc) {
        CheckSpecifyPathTerminal(t, loc, port_map, local_signals,
                                 Direction::kInput, "source",
                                 /*require_net=*/true, diag_);
      };

      auto check_destination = [&](const SpecifyTerminal& t, SourceLoc loc) {
        CheckSpecifyPathTerminal(t, loc, port_map, local_signals,
                                 Direction::kOutput, "destination",
                                 /*require_net=*/false, diag_);
      };

      auto check_timing_terminal = [&](const SpecifyTerminal& t,
                                       SourceLoc loc) {
        if (!t.interface_name.empty()) return;
        auto it = port_map.find(t.name);
        if (it != port_map.end() && it->second->direction == Direction::kRef) {
          diag_.Error(loc, std::format("ref port '{}' cannot be used as a "
                                       "terminal in a specify block",
                                       t.name));
        }
      };

      for (auto* item : mod->items) {
        if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
        for (auto* si : item->specify_items) {
          if (si->kind == SpecifyItemKind::kPathDecl) {
            for (const auto& t : si->path.src_ports) check_source(t, si->loc);
            for (const auto& t : si->path.dst_ports)
              check_destination(t, si->loc);
          } else if (si->kind == SpecifyItemKind::kTimingCheck) {
            check_timing_terminal(si->timing_check.ref_terminal, si->loc);
            check_timing_terminal(si->timing_check.data_terminal, si->loc);
          }
        }
      }

      auto same_endpoints = [](const SpecifyPathDecl& a,
                               const SpecifyPathDecl& b) {
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
      };
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
          for (auto* un : unconditionals) {
            if (same_endpoints(ifn->path, un->path)) {
              diag_.Error(ifn->loc,
                          "ifnone path conflicts with an unconditional "
                          "path on the same endpoints");
              break;
            }
          }
          if (conditionals.empty()) continue;
          bool matched = false;
          for (auto* c : conditionals) {
            if (same_endpoints(ifn->path, c->path)) {
              matched = true;
              break;
            }
          }
          if (!matched) {
            diag_.Error(ifn->loc,
                        "ifnone path endpoints do not match any companion "
                        "state-dependent path");
          }
        }
      }

      // §30.4.4.3: Different delays may be assigned to the same edge-sensitive
      // path only if every port is referenced the same way (entire port,
      // bit-select, or part-select) across all of those declarations.
      // Referencing a port as a part-select in one declaration and as a
      // bit-select in another for the same path is illegal.
      auto ref_category = [](const SpecifyTerminal& t) -> int {
        switch (t.range_kind) {
          case SpecifyRangeKind::kNone:
            return 0;  // entire port
          case SpecifyRangeKind::kBitSelect:
            return 1;  // bit-select
          default:
            return 2;  // part-select (including indexed forms)
        }
      };
      auto consistent_refs = [&](const SpecifyPathDecl& a,
                                 const SpecifyPathDecl& b) {
        for (size_t i = 0; i < a.src_ports.size(); ++i) {
          if (ref_category(a.src_ports[i]) != ref_category(b.src_ports[i]))
            return false;
        }
        for (size_t i = 0; i < a.dst_ports.size(); ++i) {
          if (ref_category(a.dst_ports[i]) != ref_category(b.dst_ports[i]))
            return false;
        }
        return true;
      };
      for (auto* item : mod->items) {
        if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
        std::vector<SpecifyItem*> edge_paths;
        for (auto* si : item->specify_items) {
          if (si->kind != SpecifyItemKind::kPathDecl) continue;
          if (si->path.edge == SpecifyEdge::kNone) continue;
          edge_paths.push_back(si);
        }
        for (size_t j = 0; j < edge_paths.size(); ++j) {
          for (size_t i = 0; i < j; ++i) {
            if (!same_endpoints(edge_paths[i]->path, edge_paths[j]->path))
              continue;
            if (!consistent_refs(edge_paths[i]->path, edge_paths[j]->path)) {
              diag_.Error(edge_paths[j]->loc,
                          "edge-sensitive paths to the same module path must "
                          "reference each port the same way (entire port, "
                          "bit-select, or part-select)");
              break;
            }
          }
        }
      }

      auto terminal_width = [&](const SpecifyTerminal& t) -> uint32_t {
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
      };
      auto sum_widths = [&](const std::vector<SpecifyTerminal>& ts,
                            bool& known) {
        uint32_t total = 0;
        for (const auto& t : ts) {
          uint32_t w = terminal_width(t);
          if (w == 0) {
            known = false;
            return uint32_t{0};
          }
          total += w;
        }
        return total;
      };
      for (auto* item : mod->items) {
        if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
        for (auto* si : item->specify_items) {
          if (si->kind != SpecifyItemKind::kPathDecl) continue;
          if (si->path.path_kind != SpecifyPathKind::kParallel) continue;
          if (si->path.data_source != nullptr) continue;
          bool src_known = true;
          bool dst_known = true;
          uint32_t src_bits = sum_widths(si->path.src_ports, src_known);
          uint32_t dst_bits = sum_widths(si->path.dst_ports, dst_known);
          if (src_known && dst_known && src_bits != dst_bits) {
            diag_.Error(si->loc,
                        "parallel path source and destination must have "
                        "equal bit widths");
          }
        }
      }

      for (auto* item : mod->items) {
        if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
        std::unordered_set<std::string_view> path_dsts;
        for (auto* si : item->specify_items) {
          if (si->kind == SpecifyItemKind::kPathDecl) {
            for (const auto& t : si->path.dst_ports) path_dsts.insert(t.name);
            continue;
          }
          if (si->kind == SpecifyItemKind::kPulsestyle) {
            for (std::string_view sig : si->signal_list) {
              if (path_dsts.contains(sig)) {
                diag_.Error(si->loc,
                            std::format("pulsestyle declaration for '{}' "
                                        "conflicts with a module path that "
                                        "drives the same output",
                                        sig));
              }
            }
            continue;
          }
          if (si->kind == SpecifyItemKind::kShowcancelled) {
            const char* kw =
                si->is_noshowcancelled ? "noshowcancelled" : "showcancelled";
            for (std::string_view sig : si->signal_list) {
              if (path_dsts.contains(sig)) {
                diag_.Error(si->loc,
                            std::format("{} declaration for '{}' conflicts "
                                        "with a module path that drives the "
                                        "same output",
                                        kw, sig));
              }
            }
          }
        }
      }

      for (auto* item : mod->items) {
        if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
        std::unordered_set<std::string_view> specparams;
        for (auto* si : item->specify_items) {
          if (si->kind == SpecifyItemKind::kSpecparam &&
              !si->param_name.empty()) {
            specparams.insert(si->param_name);
          }
        }
        std::function<void(const Expr*, SourceLoc)> check_delay_expr =
            [&](const Expr* e, SourceLoc loc) {
              if (!e) return;
              switch (e->kind) {
                case ExprKind::kIdentifier:
                  if (!specparams.contains(e->text)) {
                    diag_.Error(loc,
                                std::format("module path delay operand '{}' is "
                                            "not a specparam",
                                            e->text));
                  }
                  return;
                case ExprKind::kUnary:
                case ExprKind::kPostfixUnary:
                  check_delay_expr(e->lhs, loc);
                  return;
                case ExprKind::kBinary:
                  check_delay_expr(e->lhs, loc);
                  check_delay_expr(e->rhs, loc);
                  return;
                case ExprKind::kTernary:
                  check_delay_expr(e->condition, loc);
                  check_delay_expr(e->true_expr, loc);
                  check_delay_expr(e->false_expr, loc);
                  return;
                case ExprKind::kMinTypMax:
                  check_delay_expr(e->lhs, loc);
                  check_delay_expr(e->condition, loc);
                  check_delay_expr(e->rhs, loc);
                  return;
                case ExprKind::kSelect:
                  check_delay_expr(e->base, loc);
                  check_delay_expr(e->index, loc);
                  check_delay_expr(e->index_end, loc);
                  return;
                case ExprKind::kConcatenation:
                case ExprKind::kAssignmentPattern:
                  for (auto* el : e->elements) check_delay_expr(el, loc);
                  return;
                case ExprKind::kReplicate:
                  check_delay_expr(e->repeat_count, loc);
                  for (auto* el : e->elements) check_delay_expr(el, loc);
                  return;
                default:
                  return;
              }
            };
        for (auto* si : item->specify_items) {
          if (si->kind != SpecifyItemKind::kPathDecl) continue;
          for (auto* d : si->path.delays) check_delay_expr(d, si->loc);
        }
      }
    }
  };
  check_modules(unit_->modules);
  check_modules(unit_->interfaces);
  check_modules(unit_->programs);
}

}  // namespace delta
