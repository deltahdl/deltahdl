#include <algorithm>
#include <cmath>
#include <format>
#include <functional>
#include <map>
#include <string>
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

static ResolvedAttribute EvalAttribute(const Attribute& attr) {
  ResolvedAttribute ra;
  ra.name = attr.name;
  if (!attr.value) {
    ra.resolved_value = 1;
    return ra;
  }
  if (attr.value->kind == ExprKind::kStringLiteral) {
    auto txt = attr.value->text;
    if (txt.size() >= 2 && txt.front() == '"' && txt.back() == '"') {
      ra.string_value = txt.substr(1, txt.size() - 2);
    } else {
      ra.string_value = txt;
    }
  } else {
    ra.resolved_value = ConstEvalInt(attr.value);
  }
  return ra;
}

std::vector<ResolvedAttribute> ResolveAttributes(
    const std::vector<Attribute>& attrs, DiagEngine& diag) {
  std::vector<ResolvedAttribute> result;
  for (const auto& attr : attrs) {
    auto ra = EvalAttribute(attr);
    auto it = std::find_if(result.begin(), result.end(),
                           [&](const auto& e) { return e.name == ra.name; });
    if (it != result.end()) {
      diag.Warning(
          attr.loc,
          std::format("duplicate attribute '{}'; last value used", attr.name));
      *it = ra;
    } else {
      result.push_back(ra);
    }
  }
  return result;
}

void Elaborator::ValidateNameSpaces() {
  std::map<std::pair<std::string_view, std::string_view>, SourceRange>
      def_names;
  auto check_def = [&](std::string_view library, std::string_view name,
                       SourceRange range) {
    auto [it, inserted] = def_names.try_emplace({library, name}, range);
    if (!inserted) {
      diag_.Error(range.start,
                  std::format("duplicate definition of '{}'", name));
    }
  };
  for (auto* m : unit_->modules) check_def(m->library, m->name, m->range);
  for (auto* p : unit_->programs) check_def(p->library, p->name, p->range);
  for (auto* i : unit_->interfaces) check_def(i->library, i->name, i->range);
  for (auto* u : unit_->udps) check_def(u->library, u->name, u->range);

  for (auto* cfg : unit_->configs)
    check_def(cfg->library, cfg->name, cfg->range);

  std::unordered_set<std::string_view> pkg_names;
  for (auto* pkg : unit_->packages) {
    if (!pkg_names.insert(pkg->name).second) {
      diag_.Error(pkg->range.start,
                  std::format("duplicate package '{}'", pkg->name));
    }

    if (pkg->name == "std") {
      diag_.Error(pkg->range.start,
                  "'std' is reserved for the built-in package and cannot "
                  "be declared by the user");
    }
  }

  std::unordered_map<std::string_view, SourceLoc> cu_scope_names;
  auto check_cu = [&](std::string_view name, SourceLoc loc) {
    if (name.empty()) return;
    auto [it, inserted] = cu_scope_names.try_emplace(name, loc);
    if (!inserted) {
      diag_.Error(
          loc,
          std::format("redeclaration of '{}' in compilation-unit scope", name));
    }
  };
  for (auto* item : unit_->cu_items) {
    if (item->kind == ModuleItemKind::kImportDecl ||
        item->kind == ModuleItemKind::kExportDecl)
      continue;
    if (item->from_anonymous_program) continue;
    check_cu(item->name, item->loc);
  }
  for (auto* cls : unit_->classes) check_cu(cls->name, cls->range.start);
  for (auto* chk : unit_->checkers) check_cu(chk->name, chk->range.start);
}

void Elaborator::ValidateConfigDesignStatements() {
  std::unordered_set<std::string_view> config_names;
  for (auto* cfg : unit_->configs) config_names.insert(cfg->name);

  // A design cell is allowed to share its name with a config; when a cell of
  // that name also exists, the design statement denotes the cell rather than
  // the like-named config. A name that resolves only to a config is therefore
  // the case that must be rejected as a design target.
  std::unordered_set<std::string_view> cell_names;
  for (auto* m : unit_->modules) cell_names.insert(m->name);
  for (auto* u : unit_->udps) cell_names.insert(u->name);
  for (auto* i : unit_->interfaces) cell_names.insert(i->name);
  for (auto* p : unit_->programs) cell_names.insert(p->name);

  for (auto* cfg : unit_->configs) {
    for (auto& [lib, cell] : cfg->design_cells) {
      if (config_names.contains(cell) && !cell_names.contains(cell)) {
        diag_.Error(
            cfg->range.start,
            std::format("config '{}' design statement names configuration "
                        "'{}'; design cells must not be configs",
                        cfg->name, cell));
      }

      if (lib.empty()) {
        lib = cfg->library;
      }
    }
  }
}

void Elaborator::ValidateConfigDefaultClauses() {
  for (auto* cfg : unit_->configs) {
    int default_count = 0;
    for (auto* rule : cfg->rules) {
      if (rule->kind == ConfigRuleKind::kDefault) ++default_count;
    }
    if (default_count > 1) {
      diag_.Error(cfg->range.start,
                  std::format("config '{}' has {} default clauses; "
                              "at most one is allowed",
                              cfg->name, default_count));
    }
  }
}

void Elaborator::ValidateConfigInstanceClauses() {
  for (auto* cfg : unit_->configs) {
    if (cfg->design_cells.empty()) continue;
    std::unordered_set<std::string_view> design_cells;
    for (const auto& [lib, cell] : cfg->design_cells) {
      design_cells.insert(cell);
    }
    for (auto* rule : cfg->rules) {
      if (rule->kind != ConfigRuleKind::kInstance) continue;
      std::string_view path = rule->inst_path;
      size_t dot = path.find('.');
      std::string_view first =
          (dot == std::string_view::npos) ? path : path.substr(0, dot);
      if (!design_cells.contains(first)) {
        diag_.Error(
            cfg->range.start,
            std::format("instance path '{}' in config '{}' does not start "
                        "at a top-level cell of the config's design "
                        "statement",
                        rule->inst_path, cfg->name));
      }
    }
  }
}

void Elaborator::ValidateConfigCellClauses() {
  for (auto* cfg : unit_->configs) {
    for (auto* rule : cfg->rules) {
      if (rule->kind != ConfigRuleKind::kCell) continue;
      if (rule->cell_lib.empty()) continue;

      bool is_use_expansion = !rule->use_cell.empty() ||
                              !rule->use_lib.empty() || rule->use_config ||
                              !rule->use_params.empty();
      if (!is_use_expansion) {
        diag_.Error(cfg->range.start,
                    std::format("config '{}' cell clause '{}.{}' uses a "
                                "liblist expansion; a library-qualified "
                                "cell clause requires a use clause",
                                cfg->name, rule->cell_lib, rule->cell_name));
      }
    }
  }
}

void Elaborator::ValidateConfigPackageBinding() {
  // §33.4: a configuration's rules may redirect the binding of module,
  // primitive, interface, and program instances, but the binding of a package
  // is fixed and a config may not change it. A package is not instantiated, so
  // any clause that names a package — whether the cell selected for
  // reconfiguration or the cell an instance is bound to — is rejected.
  std::unordered_set<std::string_view> package_names;
  for (auto* pkg : unit_->packages) package_names.insert(pkg->name);
  if (package_names.empty()) return;

  for (auto* cfg : unit_->configs) {
    for (auto* rule : cfg->rules) {
      if (rule->kind == ConfigRuleKind::kCell &&
          package_names.contains(rule->cell_name)) {
        diag_.Error(
            cfg->range.start,
            std::format("config '{}' cell clause selects package '{}'; a "
                        "configuration cannot change the binding of a package",
                        cfg->name, rule->cell_name));
      }
      if (!rule->use_cell.empty() && package_names.contains(rule->use_cell)) {
        diag_.Error(
            cfg->range.start,
            std::format("config '{}' use clause binds an instance to package "
                        "'{}'; a configuration cannot change the binding of a "
                        "package",
                        cfg->name, rule->use_cell));
      }
    }
  }
}

void Elaborator::ValidateConfigHierarchicalRules() {
  for (auto* cfg : unit_->configs) {
    std::vector<std::string_view> delegated;
    for (auto* rule : cfg->rules) {
      if (rule->kind == ConfigRuleKind::kInstance && rule->use_config) {
        delegated.push_back(rule->inst_path);
      }
    }

    for (auto* rule : cfg->rules) {
      if (rule->kind != ConfigRuleKind::kInstance) continue;
      auto path = rule->inst_path;
      for (auto root : delegated) {
        if (path == root) continue;
        if (path.size() > root.size() + 1 && path.starts_with(root) &&
            path[root.size()] == '.') {
          diag_.Error(
              cfg->range.start,
              std::format("instance '{}' in config '{}' lies within "
                          "subhierarchy '{}' that is delegated to another "
                          "config",
                          path, cfg->name, root));
          break;
        }
      }
    }
  }
}

namespace {

bool IsLiteralKind(ExprKind k) {
  switch (k) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kTimeLiteral:
      return true;
    default:
      return false;
  }
}

template <typename Visitor>
bool WalkExprAny(const Expr* expr, Visitor&& v) {
  if (!expr) return false;
  if (v(expr)) return true;
  if (WalkExprAny(expr->lhs, v)) return true;
  if (WalkExprAny(expr->rhs, v)) return true;
  if (WalkExprAny(expr->condition, v)) return true;
  if (WalkExprAny(expr->true_expr, v)) return true;
  if (WalkExprAny(expr->false_expr, v)) return true;
  if (WalkExprAny(expr->base, v)) return true;
  if (WalkExprAny(expr->index, v)) return true;
  if (WalkExprAny(expr->index_end, v)) return true;
  if (WalkExprAny(expr->repeat_count, v)) return true;
  if (WalkExprAny(expr->with_expr, v)) return true;
  for (auto* a : expr->args) {
    if (WalkExprAny(a, v)) return true;
  }
  for (auto* e : expr->elements) {
    if (WalkExprAny(e, v)) return true;
  }
  return false;
}

}  // namespace

void Elaborator::ValidateConfigLocalparams() {
  for (auto* cfg : unit_->configs) {
    for (const auto& [name, expr] : cfg->local_params) {
      if (!expr) continue;
      if (!IsLiteralKind(expr->kind)) {
        diag_.Error(cfg->range.start,
                    std::format("config '{}' localparam '{}' is not assigned a "
                                "literal value",
                                cfg->name, name));
      }
    }
  }
}

void Elaborator::ValidateConfigParamOverrides() {
  for (auto* cfg : unit_->configs) {
    std::unordered_set<std::string_view> lp_names;
    for (const auto& [name, _] : cfg->local_params) lp_names.insert(name);

    auto is_pure_term_tree = [](const Expr* e) {
      while (e) {
        switch (e->kind) {
          case ExprKind::kIdentifier:
            return true;
          case ExprKind::kMemberAccess:
            e = e->lhs;
            break;
          case ExprKind::kSelect:
            e = e->base;
            break;
          default:
            return false;
        }
      }
      return false;
    };

    for (auto* rule : cfg->rules) {
      for (const auto& [pname, expr] : rule->use_params) {
        if (!expr) continue;

        bool has_hier = WalkExprAny(expr, [](const Expr* e) {
          return e->kind == ExprKind::kMemberAccess;
        });

        if (has_hier && !is_pure_term_tree(expr)) {
          diag_.Error(
              cfg->range.start,
              std::format("config '{}' override of parameter '{}' embeds a "
                          "hierarchical identifier inside a larger "
                          "expression",
                          cfg->name, pname));
        }

        bool has_mid_chain_select = WalkExprAny(expr, [](const Expr* e) {
          return e->kind == ExprKind::kMemberAccess && e->lhs &&
                 e->lhs->kind == ExprKind::kSelect;
        });
        if (has_mid_chain_select) {
          diag_.Error(
              cfg->range.start,
              std::format("config '{}' override of parameter '{}' uses a "
                          "hierarchical reference that traverses an array of "
                          "instances",
                          cfg->name, pname));
        }

        auto check_index = [&](const Expr* idx) {
          WalkExprAny(idx, [&](const Expr* sub) {
            if (sub->kind == ExprKind::kIdentifier &&
                lp_names.count(sub->text) == 0) {
              diag_.Error(
                  cfg->range.start,
                  std::format("config '{}' override of parameter '{}' uses "
                              "index identifier '{}' that is neither a "
                              "literal nor a localparam of the config",
                              cfg->name, pname, sub->text));
            }
            return false;
          });
        };
        WalkExprAny(expr, [&](const Expr* e) {
          if (e->kind == ExprKind::kSelect) {
            if (e->index) check_index(e->index);
            if (e->index_end) check_index(e->index_end);
          }
          return false;
        });

        bool has_user_call = WalkExprAny(
            expr, [](const Expr* e) { return e->kind == ExprKind::kCall; });
        if (has_user_call) {
          diag_.Error(
              cfg->range.start,
              std::format("config '{}' override of parameter '{}' calls a "
                          "user-defined function; only built-in constant "
                          "functions are permitted",
                          cfg->name, pname));
        }
      }
    }
  }
}

void Elaborator::ValidateAnonymousProgramNameSharing() {
  auto check_scope = [&](const std::vector<ModuleItem*>& items) {
    std::unordered_map<std::string_view, const ModuleItem*> seen;
    for (const auto* item : items) {
      if (item->name.empty()) continue;
      if (item->kind != ModuleItemKind::kFunctionDecl &&
          item->kind != ModuleItemKind::kTaskDecl) {
        continue;
      }
      auto [it, inserted] = seen.try_emplace(item->name, item);
      if (inserted) continue;
      if (item->from_anonymous_program || it->second->from_anonymous_program) {
        diag_.Error(
            item->loc,
            std::format(
                "'{}' declared in anonymous program collides with name in "
                "surrounding package or compilation-unit scope",
                item->name));
      }
    }
  };
  check_scope(unit_->cu_items);
  for (const auto* pkg : unit_->packages) {
    check_scope(pkg->items);
  }
}

void Elaborator::ValidatePackageItems() {
  for (const auto* pkg : unit_->packages) {
    for (const auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kNetDecl && item->init_expr) {
        diag_.Error(item->loc,
                    "net declaration with implicit continuous assignment is "
                    "not allowed in a package");
      }
      if (item->kind == ModuleItemKind::kInitialBlock ||
          item->kind == ModuleItemKind::kFinalBlock ||
          item->kind == ModuleItemKind::kAlwaysBlock ||
          item->kind == ModuleItemKind::kAlwaysCombBlock ||
          item->kind == ModuleItemKind::kAlwaysFFBlock ||
          item->kind == ModuleItemKind::kAlwaysLatchBlock) {
        diag_.Error(item->loc, "process is not allowed in a package");
      }

      if (item->kind == ModuleItemKind::kVarDecl && item->is_automatic) {
        diag_.Error(item->loc,
                    "automatic lifetime is not allowed on package-level "
                    "variables");
      }
    }
  }
}

void Elaborator::ValidatePackageReferences() {
  std::unordered_set<std::string_view> known_package_names;
  for (const auto* pkg : unit_->packages) known_package_names.insert(pkg->name);

  std::unordered_set<std::string_view> cu_top_names;
  for (const auto* item : unit_->cu_items) {
    if (!item->name.empty()) cu_top_names.insert(item->name);
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      cu_top_names.insert(item->class_decl->name);
    }
  }
  for (const auto* cls : unit_->classes) cu_top_names.insert(cls->name);

  for (const auto* pkg : unit_->packages) {
    std::unordered_set<std::string_view> pkg_names;
    std::unordered_set<std::string_view> imported_names;
    std::unordered_set<std::string_view> wildcard_pkgs;
    for (const auto* it : pkg->items) {
      if (!it->name.empty()) pkg_names.insert(it->name);
      if (it->kind == ModuleItemKind::kClassDecl && it->class_decl) {
        pkg_names.insert(it->class_decl->name);
      }
      if (it->kind == ModuleItemKind::kImportDecl) {
        if (it->import_item.is_wildcard) {
          wildcard_pkgs.insert(it->import_item.package_name);
        } else {
          imported_names.insert(it->import_item.item_name);
        }
      }
    }

    auto is_provided_by_wildcard = [&](std::string_view name) {
      for (auto pname : wildcard_pkgs) {
        for (const auto* p : unit_->packages) {
          if (p->name != pname) continue;
          for (const auto* pi : p->items) {
            if (pi->name == name) return true;
            if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
                pi->class_decl->name == name)
              return true;
          }
        }
      }
      return false;
    };

    std::function<void(const Expr*)> walk;
    walk = [&](const Expr* e) {
      if (!e) return;
      if (e->kind == ExprKind::kIdentifier) {
        if (!e->scope_prefix.empty()) {
          diag_.Error(
              e->range.start,
              std::format("package item uses scope prefix '{}', which targets "
                          "a scope outside the package",
                          e->scope_prefix));
        } else if (cu_top_names.count(e->text) && !pkg_names.count(e->text) &&
                   !imported_names.count(e->text) &&
                   !is_provided_by_wildcard(e->text)) {
          diag_.Error(
              e->range.start,
              std::format("package item references '{}' from the "
                          "compilation-unit scope; packages cannot refer to "
                          "compilation-unit-scope items",
                          e->text));
        }
      } else if (e->kind == ExprKind::kMemberAccess) {
        if (e->lhs && e->lhs->kind == ExprKind::kIdentifier && e->rhs) {
          auto root = e->lhs->text;
          bool is_pkg = known_package_names.count(root) > 0;
          bool is_self = pkg_names.count(root) > 0;
          if (!is_pkg && !is_self) {
            diag_.Error(
                e->range.start,
                std::format("package item contains a hierarchical reference "
                            "'{}' that does not target the package itself or "
                            "an imported package",
                            root));
          }
        }

        walk(e->lhs);
        walk(e->base);
        walk(e->index);
        walk(e->index_end);
        return;
      }
      walk(e->lhs);
      walk(e->rhs);
      walk(e->base);
      walk(e->index);
      walk(e->index_end);
      walk(e->condition);
      walk(e->true_expr);
      walk(e->false_expr);
      walk(e->repeat_count);
      walk(e->with_expr);
      for (const auto* a : e->args) walk(a);
      for (const auto* el : e->elements) walk(el);
    };

    for (const auto* item : pkg->items) {
      if (item->init_expr) walk(item->init_expr);
    }
  }
}

void Elaborator::ValidatePackageExports() {
  std::unordered_map<std::string_view, const PackageDecl*> pkg_by_name;
  for (const auto* pkg : unit_->packages) {
    pkg_by_name[pkg->name] = pkg;
  }

  std::function<bool(const PackageDecl*, std::string_view,
                     std::unordered_set<const PackageDecl*>&)>
      provides;
  provides = [&](const PackageDecl* src_pkg, std::string_view name,
                 std::unordered_set<const PackageDecl*>& visited) -> bool {
    if (!visited.insert(src_pkg).second) return false;
    for (const auto* it : src_pkg->items) {
      if (it->kind == ModuleItemKind::kImportDecl ||
          it->kind == ModuleItemKind::kExportDecl)
        continue;
      if (it->kind == ModuleItemKind::kClassDecl && it->class_decl &&
          it->class_decl->name == name)
        return true;
      if (!it->name.empty() && it->name == name) return true;
    }
    for (const auto* it : src_pkg->items) {
      if (it->kind != ModuleItemKind::kExportDecl) continue;
      const auto& ex = it->import_item;
      if (ex.package_name == "*") {
        for (const auto* imp : src_pkg->items) {
          if (imp->kind != ModuleItemKind::kImportDecl) continue;
          auto sit = pkg_by_name.find(imp->import_item.package_name);
          if (sit == pkg_by_name.end()) continue;
          auto sub = visited;
          if (provides(sit->second, name, sub)) return true;
        }
      } else {
        auto sit = pkg_by_name.find(ex.package_name);
        if (sit == pkg_by_name.end()) continue;
        if (ex.is_wildcard || ex.item_name == name) {
          auto sub = visited;
          if (provides(sit->second, name, sub)) return true;
        }
      }
    }
    return false;
  };

  for (const auto* pkg : unit_->packages) {
    std::unordered_set<std::string> direct_imports;
    std::unordered_set<std::string_view> wildcard_sources;
    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kImportDecl) continue;
      const auto& imp = item->import_item;
      if (imp.is_wildcard) {
        wildcard_sources.insert(imp.package_name);
      } else {
        direct_imports.insert(std::string(imp.package_name) +
                              "::" + std::string(imp.item_name));
      }
    }

    for (const auto* item : pkg->items) {
      if (item->kind != ModuleItemKind::kExportDecl) continue;
      const auto& ex = item->import_item;

      if (ex.package_name == "*" || ex.is_wildcard) continue;

      auto src_it = pkg_by_name.find(ex.package_name);
      if (src_it == pkg_by_name.end()) {
        diag_.Error(item->loc, std::format("export from unknown package '{}'",
                                           ex.package_name));
        continue;
      }
      std::unordered_set<const PackageDecl*> visited;
      if (!provides(src_it->second, ex.item_name, visited)) {
        diag_.Error(
            item->loc,
            std::format("'{}' is not a candidate for import from package '{}'",
                        ex.item_name, ex.package_name));
        continue;
      }
      auto key =
          std::string(ex.package_name) + "::" + std::string(ex.item_name);

      if (direct_imports.count(key) == 0 &&
          wildcard_sources.count(ex.package_name) == 0) {
        diag_.Error(
            item->loc,
            std::format("export '{}::{}': '{}' is not imported in package '{}'",
                        ex.package_name, ex.item_name, ex.item_name,
                        pkg->name));
      }
    }
  }
}

void Elaborator::ValidateModports() {
  auto is_literal_expr = [](const Expr* e) {
    if (!e) return false;
    switch (e->kind) {
      case ExprKind::kIntegerLiteral:
      case ExprKind::kRealLiteral:
      case ExprKind::kTimeLiteral:
      case ExprKind::kStringLiteral:
      case ExprKind::kUnbasedUnsizedLiteral:
        return true;
      default:
        return false;
    }
  };
  for (auto* iface : unit_->interfaces) {
    std::unordered_set<std::string_view> clocking_names;
    // §25.5: a modport may only reference names that this interface itself
    // declares. Collect every such name — the interface's own ports plus the
    // signals, subprograms, and other items declared in its body — so a modport
    // item naming anything outside this set can be rejected below.
    std::unordered_set<std::string_view> declared_names;
    for (const auto& port : iface->ports) {
      if (!port.name.empty()) declared_names.insert(port.name);
    }
    for (const auto* item : iface->items) {
      if (item->kind == ModuleItemKind::kClockingBlock && !item->name.empty()) {
        clocking_names.insert(item->name);
      }
      if (!item->name.empty()) declared_names.insert(item->name);
    }
    for (auto* mp : iface->modports) {
      std::unordered_set<std::string_view> port_names;
      for (const auto& port : mp->ports) {
        if (port.name.empty()) continue;
        if (!port_names.insert(port.name).second) {
          diag_.Error(mp->loc,
                      std::format("duplicate port-id '{}' in modport '{}'",
                                  port.name, mp->name));
        }
        // §25.5: a plain simple modport item (one written as a bare identifier,
        // not a `.name(expr)` modport expression, and not an imported/exported
        // subprogram or a clocking item) names an object that this interface
        // shall already declare. Naming something declared only by an enclosing
        // scope, or nowhere at all, would implicitly create a new port and is
        // illegal.
        if (!port.is_clocking && !port.is_import && !port.is_export &&
            port.expr == nullptr && !declared_names.contains(port.name)) {
          diag_.Error(
              mp->loc,
              std::format("modport '{}' references '{}', which interface '{}' "
                          "does not declare",
                          mp->name, port.name, iface->name));
        }
        if (is_literal_expr(port.expr) &&
            (port.direction == Direction::kOutput ||
             port.direction == Direction::kInout)) {
          diag_.Error(
              mp->loc,
              std::format("port-id '{}' in modport '{}' has a constant port "
                          "expression and cannot be declared as output or "
                          "inout",
                          port.name, mp->name));
        }
        if (port.is_clocking && !clocking_names.contains(port.name)) {
          diag_.Error(
              mp->loc,
              std::format("clocking identifier '{}' in modport '{}' is not "
                          "declared in interface '{}'",
                          port.name, mp->name, iface->name));
        }
      }
    }
  }
}

}  // namespace delta
