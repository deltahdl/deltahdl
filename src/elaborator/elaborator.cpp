#include "elaborator/elaborator.h"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <format>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena);

static NetType DataTypeToNetType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kTri:
      return NetType::kTri;
    case DataTypeKind::kWand:
      return NetType::kWand;
    case DataTypeKind::kWor:
      return NetType::kWor;
    case DataTypeKind::kTriand:
      return NetType::kTriand;
    case DataTypeKind::kTrior:
      return NetType::kTrior;
    case DataTypeKind::kTri0:
      return NetType::kTri0;
    case DataTypeKind::kTri1:
      return NetType::kTri1;
    case DataTypeKind::kSupply0:
      return NetType::kSupply0;
    case DataTypeKind::kSupply1:
      return NetType::kSupply1;
    case DataTypeKind::kTrireg:
      return NetType::kTrireg;
    case DataTypeKind::kUwire:
      return NetType::kUwire;
    default:
      return NetType::kWire;
  }
}

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

Elaborator::Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit)
    : arena_(arena), diag_(diag), unit_(unit) {}

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

  for (auto* cfg : unit_->configs) check_def(cfg->library, cfg->name, cfg->range);

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
        item->kind == ModuleItemKind::kExportDecl) continue;
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

}

void Elaborator::ValidateConfigLocalparams() {
  for (auto* cfg : unit_->configs) {
    for (const auto& [name, expr] : cfg->local_params) {
      if (!expr) continue;
      if (!IsLiteralKind(expr->kind)) {
        diag_.Error(
            cfg->range.start,
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

        bool has_user_call = WalkExprAny(expr, [](const Expr* e) {
          return e->kind == ExprKind::kCall;
        });
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
      if (item->from_anonymous_program ||
          it->second->from_anonymous_program) {
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
        } else if (cu_top_names.count(e->text) &&
                   !pkg_names.count(e->text) &&
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
                     std::unordered_set<const PackageDecl*>&)> provides;
  provides = [&](const PackageDecl* src_pkg, std::string_view name,
                 std::unordered_set<const PackageDecl*>& visited) -> bool {
    if (!visited.insert(src_pkg).second) return false;
    for (const auto* it : src_pkg->items) {
      if (it->kind == ModuleItemKind::kImportDecl ||
          it->kind == ModuleItemKind::kExportDecl) continue;
      if (it->kind == ModuleItemKind::kClassDecl && it->class_decl &&
          it->class_decl->name == name) return true;
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
        diag_.Error(item->loc,
                    std::format("export from unknown package '{}'",
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
      auto key = std::string(ex.package_name) + "::" + std::string(ex.item_name);

      if (direct_imports.count(key) == 0 &&
          wildcard_sources.count(ex.package_name) == 0) {
        diag_.Error(
            item->loc,
            std::format(
                "export '{}::{}': '{}' is not imported in package '{}'",
                ex.package_name, ex.item_name, ex.item_name, pkg->name));
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
      if (item->kind == ModuleItemKind::kClockingBlock &&
          !item->name.empty()) {
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
        if (!t.interface_name.empty()) return;
        auto it = port_map.find(t.name);
        if (it != port_map.end()) {
          const PortDecl* p = it->second;
          if (p->direction == Direction::kRef) {
            diag_.Error(loc,
                        std::format("ref port '{}' cannot be used as a "
                                    "terminal in a specify block",
                                    t.name));
            return;
          }
          if (p->direction != Direction::kInput &&
              p->direction != Direction::kInout) {
            diag_.Error(loc,
                        std::format("module path source '{}' must be "
                                    "connected to an input or inout port",
                                    t.name));
            return;
          }
          bool is_var = !p->data_type.is_net && !p->data_type.is_interconnect;
          if (is_var) {
            diag_.Error(loc,
                        std::format("module path source '{}' must be a net",
                                    t.name));
          }
          return;
        }
        if (local_signals.contains(t.name)) {
          diag_.Error(loc,
                      std::format("module path source '{}' is not connected "
                                  "to an input or inout port",
                                  t.name));
        }
      };

      auto check_destination = [&](const SpecifyTerminal& t, SourceLoc loc) {
        if (!t.interface_name.empty()) return;
        auto it = port_map.find(t.name);
        if (it != port_map.end()) {
          const PortDecl* p = it->second;
          if (p->direction == Direction::kRef) {
            diag_.Error(loc,
                        std::format("ref port '{}' cannot be used as a "
                                    "terminal in a specify block",
                                    t.name));
            return;
          }
          if (p->direction != Direction::kOutput &&
              p->direction != Direction::kInout) {
            diag_.Error(loc,
                        std::format("module path destination '{}' must be "
                                    "connected to an output or inout port",
                                    t.name));
          }
          return;
        }
        if (local_signals.contains(t.name)) {
          diag_.Error(loc,
                      std::format("module path destination '{}' is not "
                                  "connected to an output or inout port",
                                  t.name));
        }
      };

      auto check_timing_terminal = [&](const SpecifyTerminal& t,
                                       SourceLoc loc) {
        if (!t.interface_name.empty()) return;
        auto it = port_map.find(t.name);
        if (it != port_map.end() && it->second->direction == Direction::kRef) {
          diag_.Error(loc,
                      std::format("ref port '{}' cannot be used as a "
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
          if (w == 0) { known = false; return uint32_t{0}; }
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

static void CollectAllModules(
    RtlirModule* mod,
    std::unordered_map<std::string_view, RtlirModule*>& all_modules) {
  if (!mod) return;
  auto [it, inserted] = all_modules.try_emplace(mod->name, mod);
  if (!inserted) return;
  for (auto& child : mod->children) {
    CollectAllModules(child.resolved, all_modules);
  }
}

void Elaborator::RunPreElaborationValidations() {

  ValidateNameSpaces();

  ValidateConfigDesignStatements();

  ValidateConfigDefaultClauses();

  ValidateConfigInstanceClauses();

  ValidateConfigCellClauses();

  ValidateConfigPackageBinding();

  ValidateConfigHierarchicalRules();

  ValidateConfigLocalparams();

  ValidateConfigParamOverrides();

  ValidateAnonymousProgramNameSharing();

  ValidateAnonymousProgramHierRefs();

  ValidatePackageItems();

  ValidatePackageReferences();

  ValidatePackageExports();

  ValidateModports();

  ValidateSpecifyBlocks();

  RegisterCuScopeItems();

  ApplyClassMethodAutomaticDefault();

  ValidateFinalClassExtension();

  ValidateWeakReferenceMembers();

  ValidateChainingConstructors();

  ValidateEmbeddedCovergroupAssign();

  ValidateDerivedCovergroupBase();

  ValidateConstClassProperties();

  ValidateVirtualMethodOverrides();

  ValidateAbstractClassRules();

  ValidateOutOfBlockDeclarations();

  ValidateInterfaceClassRules();

  ValidateRandomVariableTypes();

  ValidateConstraintBlockNames();

  ValidateForeachConstraintDims();

  ValidateSolveBeforeConstraints();

  ValidateSoftConstraintVariables();

  ValidateConstraintFunctionArgs();

  ValidateBuiltinRandomizationMethods();

  ValidateExternalConstraints();

  ValidateConstraintInheritance();

  ValidateForwardClassTypedefs();

  ValidateTimescaleConsistency();

  ValidateDpiDeclarations();

  ValidateDpiGlobalNameSpace();

  ResolveExternModules();
}

RtlirDesign* Elaborator::ElaborateTops(
    const std::vector<ModuleDecl*>& top_decls) {
  auto* design = arena_.Create<RtlirDesign>();
  ParamList empty_params;
  pending_generates_.clear();
  applied_defparams_.clear();
  early_defparam_resolutions_.clear();

  for (auto* mod_decl : top_decls) {

    std::string saved_path = std::move(current_inst_path_);
    current_inst_path_.assign(mod_decl->name.data(), mod_decl->name.size());
    auto* top = ElaborateModule(mod_decl, empty_params);
    current_inst_path_ = std::move(saved_path);
    if (!top) return nullptr;
    design->top_modules.push_back(top);
  }

  while (true) {
    for (auto* top : design->top_modules) {
      ApplyDefparamsRecursively(top);
    }
    if (pending_generates_.empty()) break;
    std::vector<PendingGenerate> batch;
    batch.swap(pending_generates_);
    for (auto& pg : batch) {
      ProcessPendingGenerate(pg.item, pg.mod);
    }
  }
  VerifyEarlyResolvedDefparams();

  for (auto* top : design->top_modules) {
    WarnUnresolvedDefparams(top);

    ApplyBindDirectives(top);

    ValidateModportExportConflicts(top);

    CollectAllModules(top, design->all_modules);
  }

  // §23.10.4.2: detect defparam hierarchical names whose early resolution would
  // diverge from the fully elaborated hierarchy. all_modules holds each
  // instantiated module once, so each module's defparams are checked a single
  // time regardless of how many instances exist.
  {
    std::unordered_set<std::string_view> top_names;
    for (auto* top : design->top_modules) top_names.insert(top->name);
    for (const auto& entry : design->all_modules)
      CheckEarlyResolutionAmbiguity(entry.second, top_names);
  }

  for (auto* item : unit_->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      design->cu_function_decls.push_back(item);
    } else if (item->kind == ModuleItemKind::kLetDecl) {
      ValidateLetDecl(item);
      design->cu_let_decls.push_back(item);
    }
  }

  for (const auto& [name, dtype] : typedefs_) {
    design->type_widths[name] = EvalTypeWidth(dtype, typedefs_);
  }

  design->packages = unit_->packages;

  design->cu_class_decls.insert(design->cu_class_decls.end(),
                                unit_->classes.begin(), unit_->classes.end());
  design->simulation_blocked = elab_simulation_blocked_;
  design->last_elab_severity = elab_last_severity_;
  design->last_elab_severity_msg = elab_last_severity_msg_;
  design->last_elab_severity_scope = elab_last_severity_scope_;
  design->last_elab_severity_loc = elab_last_severity_loc_;
  return design;
}

RtlirDesign* Elaborator::Elaborate(std::string_view top_module_name) {
  RunPreElaborationValidations();

  auto* mod_decl = FindModule(top_module_name);
  if (!mod_decl) {
    diag_.Error({}, std::format("top module '{}' not found", top_module_name));
    return nullptr;
  }
  return ElaborateTops({mod_decl});
}

void Elaborator::SetLibraryDeclarationOrder(std::vector<std::string> order) {
  library_order_ = std::move(order);
}

RtlirDesign* Elaborator::Elaborate(const ConfigDecl* cfg) {
  in_config_elaboration_ = true;
  RunPreElaborationValidations();

  // A config localparam is restricted to a literal value (§33.4.3), so it can
  // be evaluated once here and made available to parameter-override
  // expressions that reference it.
  for (const auto& [name, expr] : cfg->local_params) {
    if (!expr) continue;
    if (auto val = ConstEvalInt(expr, config_localparam_scope_)) {
      config_localparam_scope_[name] = *val;
    }
  }

  // Record the parameter overrides each instance clause carries so they can be
  // applied as the matching instance is elaborated (§33.4.3).
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (rule->use_params.empty() && !rule->use_param_reset_all) continue;
    ConfigParamOverride ov;
    ov.inst_path.assign(rule->inst_path.data(), rule->inst_path.size());
    ov.reset_all = rule->use_param_reset_all;
    ov.params = rule->use_params;
    instance_param_overrides_.push_back(std::move(ov));
  }

  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kDefault) continue;
    library_order_.clear();
    library_order_.reserve(rule->liblist.size());
    for (auto lib : rule->liblist) {
      library_order_.emplace_back(lib);
    }
    library_order_strict_ = true;
    break;
  }

  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kCell) continue;
    // A cell clause carrying a use expansion rebinds a cell. A target cell is
    // required; the target library may be omitted, in which case it is
    // inherited from the parent cell (§33.4.1.6). The qualifying library, when
    // present, scopes which instances the clause applies to (§33.4.1.4).
    if (!rule->use_cell.empty()) {
      cell_clause_use_overrides_[std::string(rule->cell_name)] = {
          std::string(rule->cell_lib), std::string(rule->use_lib),
          std::string(rule->use_cell)};
      continue;
    }
    // Otherwise the cell clause selects a library list to search for the named
    // cell (§33.4.1.4 selecting the list of §33.4.1.5).
    std::vector<std::string> libs;
    libs.reserve(rule->liblist.size());
    for (auto lib : rule->liblist) libs.emplace_back(lib);
    cell_clause_liblist_overrides_[std::string(rule->cell_name)] =
        std::move(libs);
  }

  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (rule->liblist.empty()) continue;
    std::vector<std::string> libs;
    libs.reserve(rule->liblist.size());
    for (auto lib : rule->liblist) libs.emplace_back(lib);
    instance_liblist_overrides_.emplace_back(std::string(rule->inst_path),
                                             std::move(libs));
  }

  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (!rule->use_config) continue;
    const ConfigDecl* inner = nullptr;
    for (auto* other : unit_->configs) {
      if (other != cfg && other->name == rule->use_cell) {
        inner = other;
        break;
      }
    }
    if (!inner) {
      diag_.Error(cfg->range.start,
                  std::format("config '{}' delegates instance '{}' to unknown "
                              "config '{}'",
                              cfg->name, rule->inst_path, rule->use_cell));
      continue;
    }
    if (inner->design_cells.empty()) continue;
    std::string outer_path(rule->inst_path);
    const auto& [inner_lib, inner_cell] = inner->design_cells.front();
    instance_use_overrides_.emplace_back(outer_path, std::string(inner_lib),
                                         std::string(inner_cell));

    std::string_view inner_top = inner_cell;
    for (auto* irule : inner->rules) {
      if (irule->kind == ConfigRuleKind::kDefault) {
        if (irule->liblist.empty()) continue;
        std::vector<std::string> libs;
        libs.reserve(irule->liblist.size());
        for (auto lib : irule->liblist) libs.emplace_back(lib);
        instance_liblist_overrides_.emplace_back(outer_path, std::move(libs));
      } else if (irule->kind == ConfigRuleKind::kInstance) {
        if (irule->liblist.empty()) continue;
        std::string_view ipath = irule->inst_path;
        bool path_matches =
            ipath == inner_top ||
            (ipath.size() > inner_top.size() && ipath.starts_with(inner_top) &&
             ipath[inner_top.size()] == '.');
        if (!path_matches) continue;
        std::string translated = outer_path;
        if (ipath.size() > inner_top.size()) {
          translated.append(ipath.substr(inner_top.size()));
        }
        std::vector<std::string> libs;
        libs.reserve(irule->liblist.size());
        for (auto lib : irule->liblist) libs.emplace_back(lib);
        instance_liblist_overrides_.emplace_back(std::move(translated),
                                                 std::move(libs));
      }
    }
  }

  std::vector<ModuleDecl*> top_decls;
  top_decls.reserve(cfg->design_cells.size());
  for (const auto& [lib, cell] : cfg->design_cells) {
    auto* md = FindModule(cell);
    if (!md) {
      diag_.Error({}, std::format("config '{}' design cell '{}' not found",
                                  cfg->name, cell));
      return nullptr;
    }
    top_decls.push_back(md);
  }
  return ElaborateTops(top_decls);
}

void Elaborator::RegisterCuScopeItems() {

  class_names_.insert("semaphore");

  class_names_.insert("mailbox");

  class_names_.insert("weak_reference");

  class_names_.insert("process");
  for (auto* item : unit_->cu_items) {
    if (!item->name.empty()) cu_scope_names_.insert(item->name);
    if (item->kind == ModuleItemKind::kTypedef) {
      typedefs_[item->name] = item->typedef_type;
    } else if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      class_names_.insert(item->class_decl->name);
      if (!item->class_decl->params.empty())
        parameterized_class_names_.insert(item->class_decl->name);
    } else if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
      auto val = ConstEvalInt(item->init_expr, cu_param_scope_);
      if (val) {
        cu_param_scope_[item->name] = *val;
      }
    }
  }
  for (auto* cls : unit_->classes) {
    class_names_.insert(cls->name);
    cu_scope_names_.insert(cls->name);
    if (!cls->params.empty()) parameterized_class_names_.insert(cls->name);
  }

  for (auto* pkg : unit_->packages) {
    for (auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
        auto val = ConstEvalInt(item->init_expr, cu_param_scope_);
        if (val) {
          auto* qname = arena_.Create<std::string>(
              std::string(pkg->name) + "." + std::string(item->name));
          cu_param_scope_[*qname] = *val;
        }
      }
    }
  }
}

ModuleItem* Elaborator::FindCuScopeItem(std::string_view name) const {
  for (auto* item : unit_->cu_items) {
    if (item->name == name) return item;
  }
  return nullptr;
}

// Two port data types correspond for extern-declaration matching when they
// share a base kind, signedness, and (for named types) the same type name.
// Packed/unpacked dimension sizes are parameter-dependent expressions that are
// not yet evaluated here, so only the dimension-independent attributes that the
// parser records are compared.
static bool ExternPortTypesEquivalent(const DataType& a, const DataType& b) {
  return a.kind == b.kind && a.is_signed == b.is_signed &&
         a.type_name == b.type_name;
}

void Elaborator::ResolveExternModules() {
  for (auto* mod : unit_->modules) {
    if (mod->is_extern) continue;

    ModuleDecl* extern_decl = nullptr;
    for (auto* other : unit_->modules) {
      if (other->is_extern && other->name == mod->name) {
        extern_decl = other;
        break;
      }
    }
    if (!extern_decl) continue;

    if (mod->has_wildcard_ports) {
      mod->ports = extern_decl->ports;
      if (mod->params.empty() && !extern_decl->params.empty()) {
        mod->params = extern_decl->params;
        mod->type_param_names = extern_decl->type_param_names;
        mod->has_param_port_list = extern_decl->has_param_port_list;
      }
      continue;
    }

    if (extern_decl->ports.size() != mod->ports.size()) {
      diag_.Error(mod->range.start,
                  std::format("module '{}' port count ({}) does not match "
                              "extern declaration ({})",
                              mod->name, mod->ports.size(),
                              extern_decl->ports.size()));
      continue;
    }
    for (size_t i = 0; i < mod->ports.size(); ++i) {
      const PortDecl& ep = extern_decl->ports[i];
      const PortDecl& mp = mod->ports[i];
      if (!mp.name.empty() && !ep.name.empty() && mp.name != ep.name) {
        diag_.Error(mod->range.start,
                    std::format("module '{}' port '{}' at position {} does not "
                                "match extern declaration port '{}'",
                                mod->name, mp.name, i, ep.name));
        break;
      }
      // §23.5 requires the extern declaration to match the actual module in the
      // equivalent types of corresponding ports. Direction and data type are
      // only compared when the extern header states them: a non-ANSI extern
      // port list supplies names and positions alone and leaves the type to the
      // actual definition, so an unspecified side is treated as a match.
      if (ep.direction != Direction::kNone && mp.direction != Direction::kNone &&
          ep.direction != mp.direction) {
        diag_.Error(mp.loc,
                    std::format("module '{}' port '{}' direction does not match "
                                "extern declaration",
                                mod->name, mp.name));
        break;
      }
      if (ep.data_type.kind != DataTypeKind::kImplicit &&
          mp.data_type.kind != DataTypeKind::kImplicit &&
          !ExternPortTypesEquivalent(ep.data_type, mp.data_type)) {
        diag_.Error(mp.loc,
                    std::format("module '{}' port '{}' type does not match "
                                "extern declaration",
                                mod->name, mp.name));
        break;
      }
    }
    if (extern_decl->params.size() != mod->params.size()) {
      diag_.Error(
          mod->range.start,
          std::format("module '{}' parameter count ({}) does not match "
                      "extern declaration ({})",
                      mod->name, mod->params.size(),
                      extern_decl->params.size()));
    } else {
      // The parameter lists must also correspond by name and position.
      for (size_t i = 0; i < mod->params.size(); ++i) {
        std::string_view mp_name = mod->params[i].first;
        std::string_view ep_name = extern_decl->params[i].first;
        if (!mp_name.empty() && !ep_name.empty() && mp_name != ep_name) {
          diag_.Error(mod->range.start,
                      std::format("module '{}' parameter '{}' at position {} "
                                  "does not match extern declaration "
                                  "parameter '{}'",
                                  mod->name, mp_name, i, ep_name));
          break;
        }
        // §23.5 also calls for equivalent parameter types. A type parameter and
        // a value parameter at the same position are not equivalent, so the
        // two declarations must agree on whether each entry is a type
        // parameter.
        bool mp_is_type = mod->type_param_names.count(mp_name) != 0;
        bool ep_is_type = extern_decl->type_param_names.count(ep_name) != 0;
        if (mp_is_type != ep_is_type) {
          diag_.Error(mod->range.start,
                      std::format("module '{}' parameter '{}' at position {} "
                                  "does not match the parameter kind of the "
                                  "extern declaration",
                                  mod->name, mp_name, i));
          break;
        }
      }
    }
  }
}

std::optional<ModuleDecl*> Elaborator::ResolveCellUseOverride(
    std::string_view name) const {
  auto it = cell_clause_use_overrides_.find(std::string(name));
  if (it == cell_clause_use_overrides_.end()) return std::nullopt;
  const auto& ov = it->second;

  // A library-qualified cell clause applies only to the cell as defined in
  // that library (§33.4.1.4); if no such cell exists the clause matches
  // nothing and resolution proceeds normally.
  bool applies = ov.src_lib.empty();
  if (!applies) {
    for (auto* mod : unit_->modules) {
      if (mod->name != name) continue;
      if (mod->library == ov.src_lib) {
        applies = true;
        break;
      }
    }
  }
  if (!applies) return std::nullopt;

  // An omitted target library is inherited from the parent cell (§33.4.1.6).
  std::string_view target_lib = ov.use_lib.empty()
                                    ? std::string_view(current_library_)
                                    : std::string_view(ov.use_lib);
  for (auto* mod : unit_->modules) {
    if (mod->is_extern) continue;
    if (mod->library == target_lib && mod->name == ov.use_cell) return mod;
  }
  return static_cast<ModuleDecl*>(nullptr);
}

ModuleDecl* Elaborator::FindModule(std::string_view name) const {

  if (!current_inst_path_.empty()) {
    for (const auto& [path, ulib, ucell] : instance_use_overrides_) {
      if (path != current_inst_path_) continue;
      if (name != ucell) continue;
      for (auto* mod : unit_->modules) {
        if (mod->is_extern) continue;
        if (mod->library == ulib && mod->name == ucell) return mod;
      }
      return nullptr;
    }
  }

  if (auto hit = ResolveCellUseOverride(name); hit.has_value()) {
    return *hit;
  }

  ModuleDecl* extern_decl = nullptr;
  std::vector<ModuleDecl*> candidates;
  for (auto* mod : unit_->modules) {
    if (mod->name != name) continue;
    if (mod->is_extern) {
      if (!extern_decl) extern_decl = mod;
    } else {
      candidates.push_back(mod);
    }
  }

  const std::vector<std::string>* override_liblist = nullptr;
  size_t best_match_len = 0;
  if (!current_inst_path_.empty()) {
    for (const auto& [rule_path, libs] : instance_liblist_overrides_) {
      bool matches = false;
      if (current_inst_path_ == rule_path) {
        matches = true;
      } else if (current_inst_path_.size() > rule_path.size() &&
                 current_inst_path_.compare(0, rule_path.size(), rule_path)
                     == 0 &&
                 current_inst_path_[rule_path.size()] == '.') {
        matches = true;
      }
      if (matches && rule_path.size() >= best_match_len) {
        override_liblist = &libs;
        best_match_len = rule_path.size();
      }
    }
  }

  // Absent an instance-scoped library list, a cell selection clause may name
  // the library list for this cell (§33.4.1.4, §33.4.1.5).
  if (override_liblist == nullptr) {
    if (auto it = cell_clause_liblist_overrides_.find(std::string(name));
        it != cell_clause_liblist_overrides_.end()) {
      override_liblist = &it->second;
    }
  }

  if (override_liblist != nullptr && !candidates.empty()) {
    std::vector<ModuleDecl*> filtered;
    filtered.reserve(candidates.size());
    for (auto* c : candidates) {
      for (const auto& lib : *override_liblist) {
        if (lib == c->library) {
          filtered.push_back(c);
          break;
        }
      }
    }
    candidates = std::move(filtered);
    if (!candidates.empty()) {
      auto pri = [override_liblist](std::string_view lib) -> size_t {
        for (size_t i = 0; i < override_liblist->size(); ++i) {
          if ((*override_liblist)[i] == lib) return i;
        }
        return override_liblist->size();
      };
      ModuleDecl* best = candidates.front();
      size_t best_pri = pri(best->library);
      for (size_t i = 1; i < candidates.size(); ++i) {
        size_t p = pri(candidates[i]->library);
        if (p < best_pri) {
          best = candidates[i];
          best_pri = p;
        }
      }
      return best;
    }
  } else {

    // An empty selected library list selects no libraries to filter against;
    // it is treated below as no list being selected (§33.4.1.5).
    if (library_order_strict_ && !library_order_.empty() &&
        !candidates.empty()) {
      std::vector<ModuleDecl*> filtered;
      filtered.reserve(candidates.size());
      for (auto* c : candidates) {
        bool listed = false;
        for (const auto& lib : library_order_) {
          if (lib == c->library) {
            listed = true;
            break;
          }
        }
        if (listed) filtered.push_back(c);
      }
      candidates = std::move(filtered);
    }
    if (!candidates.empty()) {
      // §33.4.1.5: when no library list clause is selected (or the selected
      // list is empty), the list holds only the parent cell's library, so an
      // instance binds to the cell defined in its parent's library.
      bool no_list_selected = !library_order_strict_ || library_order_.empty();
      if (in_config_elaboration_ && no_list_selected &&
          !current_library_.empty()) {
        for (auto* c : candidates) {
          if (c->library == current_library_) return c;
        }
      }
      auto priority = [this](std::string_view lib) -> size_t {
        for (size_t i = 0; i < library_order_.size(); ++i) {
          if (library_order_[i] == lib) return i;
        }
        return library_order_.size();
      };
      ModuleDecl* best = candidates.front();
      size_t best_pri = priority(best->library);
      for (size_t i = 1; i < candidates.size(); ++i) {
        size_t pri = priority(candidates[i]->library);
        if (pri < best_pri) {
          best = candidates[i];
          best_pri = pri;
        }
      }
      return best;
    }
  }
  if (extern_decl) return extern_decl;

  auto pit = std::find_if(unit_->programs.begin(), unit_->programs.end(),
                          [name](auto* p) { return p->name == name; });
  if (pit != unit_->programs.end()) return *pit;

  auto iit = std::find_if(unit_->interfaces.begin(), unit_->interfaces.end(),
                          [name](auto* i) { return i->name == name; });
  if (iit != unit_->interfaces.end()) return *iit;

  auto cit = std::find_if(unit_->checkers.begin(), unit_->checkers.end(),
                          [name](auto* c) { return c->name == name; });
  if (cit != unit_->checkers.end()) return *cit;

  return nullptr;
}

ModuleDecl* Elaborator::FindModuleInScope(std::string_view name) const {
  auto it = nested_module_decls_.find(name);
  if (it != nested_module_decls_.end()) return it->second;
  return FindModule(name);
}

static std::optional<int64_t> FindParamOverride(
    const Elaborator::ParamList& params, std::string_view name) {
  for (const auto& [oname, oval] : params) {
    if (oname == name) {
      return oval;
    }
  }
  return std::nullopt;
}

bool Elaborator::HasParamPortWithoutDefault(const ModuleDecl* decl) {
  for (const auto& [name, expr] : decl->params) {
    if (decl->localparam_port_names.count(name)) continue;
    if (decl->type_param_names.count(name)) continue;
    if (expr == nullptr) return true;
  }
  return false;
}

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype) {
  pd.has_decl_range = dtype.packed_dim_left != nullptr;
  pd.has_decl_type = dtype.kind != DataTypeKind::kImplicit || dtype.is_signed;
  pd.decl_is_signed = dtype.is_signed;
  pd.decl_type_implicit = dtype.kind == DataTypeKind::kImplicit;
  if (pd.has_decl_range || pd.has_decl_type) {
    pd.decl_width = EvalTypeWidth(dtype);
  }
}

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype,
                           const TypedefMap& typedefs,
                           const ScopeMap& scope) {
  pd.has_decl_range = dtype.packed_dim_left != nullptr;
  pd.has_decl_type = dtype.kind != DataTypeKind::kImplicit || dtype.is_signed;
  pd.decl_is_signed = dtype.is_signed;
  pd.decl_type_implicit = dtype.kind == DataTypeKind::kImplicit;
  if (pd.has_decl_range || pd.has_decl_type) {
    pd.decl_width = EvalTypeWidth(dtype, typedefs, scope);
  }
}

bool ParamExpectsIntegerValue(const RtlirParamDecl& pd, const DataType& dtype) {
  // §6.20.2: a value parameter is in an integer context — and so subject to the
  // real-to-integer conversion of §6.12.1 — when it carries a packed range or
  // an explicit non-real data type. A bare (untyped) parameter or one declared
  // real takes a real value instead and is not converted here.
  return pd.has_decl_range || (pd.has_decl_type && !IsRealType(dtype.kind));
}

int64_t ConvertOverrideValue(int64_t value, const RtlirParamDecl& pd) {
  // §6.20.2: a parameter declared with an explicit range, or with an explicit
  // (non-implicit) data type, keeps the sign and range of its declaration; a
  // value override does not change them, so the incoming value is coerced into
  // the declared width. A parameter with no range and only an implicit type
  // (including a bare `signed`) instead takes its range from the final value
  // assigned, so the override value passes through unchanged.
  bool has_fixed_width =
      pd.has_decl_range || (pd.has_decl_type && !pd.decl_type_implicit);
  if (!has_fixed_width) return value;
  uint32_t w = pd.decl_width;
  if (w == 0 || w >= 64) return value;
  uint64_t mask = (uint64_t{1} << w) - 1;
  uint64_t masked = static_cast<uint64_t>(value) & mask;
  if (pd.decl_is_signed) {
    uint64_t sign_bit = uint64_t{1} << (w - 1);
    if (masked & sign_bit) masked |= ~mask;
  }
  return static_cast<int64_t>(masked);
}

void Elaborator::ApplyHeaderImports(const ModuleDecl* decl) {
  auto register_item = [&](const ModuleItem* pi, std::string_view name) {
    if (pi->kind == ModuleItemKind::kTypedef) {
      typedefs_[name] = pi->typedef_type;
    } else if (pi->kind == ModuleItemKind::kParamDecl && pi->init_expr) {
      auto val = ConstEvalInt(pi->init_expr, cu_param_scope_);
      if (val) cu_param_scope_[name] = *val;
    }
  };

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_header) continue;
    auto pkg_name = item->import_item.package_name;
    const ModuleDecl* pkg = nullptr;
    for (const auto* p : unit_->packages) {
      if (p->name == pkg_name) { pkg = p; break; }
    }
    if (!pkg) continue;
    if (item->import_item.is_wildcard) {
      for (const auto* pi : pkg->items) {
        if (!pi->name.empty()) register_item(pi, pi->name);
      }
    } else {
      auto target = item->import_item.item_name;
      for (const auto* pi : pkg->items) {
        if (pi->name == target) {
          register_item(pi, target);
          break;
        }
      }
    }
  }
}

// §23.2.2.3: an explicitly named port (.name(expr)) takes the self-determined
// data type of its connection expression. Resolve the expression's width
// against the module's already-elaborated variables and nets. Returns 0 when
// the width cannot be determined here, leaving the port's default untouched.
static uint32_t ExplicitPortExprWidth(const Expr* expr, const RtlirModule* mod) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      for (const auto& v : mod->variables)
        if (v.name == expr->text) return v.width;
      for (const auto& n : mod->nets)
        if (n.name == expr->text) return n.width;
      return 0;
    case ExprKind::kConcatenation: {
      uint32_t total = 0;
      for (const auto* el : expr->elements)
        total += ExplicitPortExprWidth(el, mod);
      return total;
    }
    default:
      return 0;
  }
}

// The self-determined signedness of an explicit port expression: a simple
// reference adopts the referenced object's signedness; composite expressions
// such as concatenations are unsigned.
static bool ExplicitPortExprSigned(const Expr* expr, const RtlirModule* mod) {
  if (!expr || expr->kind != ExprKind::kIdentifier) return false;
  for (const auto& v : mod->variables)
    if (v.name == expr->text) return v.is_signed;
  for (const auto& n : mod->nets)
    if (n.name == expr->text) return n.is_signed;
  return false;
}

// §23.2.2.3: apply the self-determined type of each explicitly named port's
// connection expression to the resolved port. The referenced declarations live
// in the module body, so this runs after the items have been elaborated.
static void ResolveExplicitPortTypes(const ModuleDecl* decl, RtlirModule* mod) {
  for (const auto& src : decl->ports) {
    if (!src.is_explicit_named || !src.port_expr || src.name.empty()) continue;
    uint32_t w = ExplicitPortExprWidth(src.port_expr, mod);
    if (w == 0) continue;
    for (auto& rp : mod->ports) {
      if (rp.name != src.name) continue;
      rp.type_kind = DataTypeKind::kLogic;
      rp.width = w;
      rp.is_signed = ExplicitPortExprSigned(src.port_expr, mod);
      break;
    }
  }
}

RtlirModule* Elaborator::ElaborateModule(const ModuleDecl* decl,
                                         const ParamList& params) {
  auto* mod = arena_.Create<RtlirModule>();
  mod->name = decl->name;

  mod->library = decl->library;

  // While this cell is elaborated it is the parent of any instances it
  // contains; record its library so child binding can fall back to it
  // (§33.4.1.5) or inherit it for a library-less use clause (§33.4.1.6). The
  // previous value is restored before returning.
  std::string saved_library = std::move(current_library_);
  current_library_.assign(decl->library.data(), decl->library.size());
  mod->has_param_port_list = decl->has_param_port_list;
  mod->is_program = (decl->decl_kind == ModuleDeclKind::kProgram);

  mod->delay_mode = unit_->delay_mode_directive;

  mod->attrs = ResolveAttributes(decl->attrs, diag_);

  RtlirImport std_import;
  std_import.package_name = "std";
  std_import.is_wildcard = true;
  mod->imports.push_back(std_import);

  ApplyHeaderImports(decl);

  for (size_t i = 0; i < decl->params.size(); ++i) {
    const auto& [pname, pval] = decl->params[i];
    RtlirParamDecl pd;
    pd.name = pname;
    pd.default_value = pval;
    pd.is_resolved = false;
    pd.is_type_param = decl->type_param_names.count(pname) > 0;
    pd.is_localparam = decl->localparam_port_names.count(pname) > 0;

    auto scope = BuildParamScope(mod);

    if (!pd.is_type_param && i < decl->param_types.size()) {
      PopulateParamTypeInfo(pd, decl->param_types[i], typedefs_, scope);
    }

    auto override_val = FindParamOverride(params, pname);
    if (override_val) {
      pd.resolved_value = ConvertOverrideValue(*override_val, pd);
      pd.is_resolved = true;
      pd.from_override = true;
    }
    if (!pd.is_resolved && pval) {
      if (pval->kind == ExprKind::kIdentifier && pval->text == "$") {
        pd.is_unbounded = true;
      } else if (pval->kind == ExprKind::kIdentifier &&
                 RefersToUnboundedParam(mod, pval->text)) {
        // §6.20.7: assigning a $ (unbounded) parameter to another parameter is
        // legal; the assigned-to parameter is itself unbounded.
        pd.is_unbounded = true;
      } else {
        if (ContainsDollarSubexpr(pval)) {
          // §6.20.7: $ must be the entire, self-contained parameter value; it
          // may not be combined with operators or selects in this context.
          diag_.Error(pval->range.start,
                      std::format("'$' may only be assigned to parameter '{}' "
                                  "as a complete, self-contained expression",
                                  pname));
        }
        auto val = ConstEvalInt(pval, scope);
        if (val) {
          pd.resolved_value = *val;
          pd.is_resolved = true;
        } else if (!pd.is_type_param && i < decl->param_types.size() &&
                   ParamExpectsIntegerValue(pd, decl->param_types[i])) {
          // §6.20.2: an integer-typed parameter set from a real constant is
          // converted to an integer per §6.12.1 (round to nearest, ties away
          // from zero).
          if (auto rval = ConstEvalReal(pval, scope)) {
            pd.resolved_value = std::llround(*rval);
            pd.is_resolved = true;
          }
        }
      }
    }

    mod->params.push_back(pd);
  }

  for (const auto& pd : mod->params) {
    if (pd.is_localparam || pd.is_type_param) continue;
    if (pd.default_value != nullptr) continue;
    if (pd.from_override) continue;
    diag_.Error(decl->range.start,
                std::format("parameter '{}' of '{}' has no default value and "
                            "no override at instantiation",
                            pd.name, decl->name));
  }

  ElaboratePorts(decl, mod);

  CheckConditionalGenerateNaming(decl);
  AssignGenerateBlockNames(decl);
  ElaborateItems(decl, mod);
  ResolveExplicitPortTypes(decl, mod);
  current_library_ = std::move(saved_library);
  return mod;
}

void Elaborator::ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod) {
  auto param_scope = BuildParamScope(mod);

  if (decl->is_non_ansi_ports) {
    std::unordered_set<std::string_view> explicit_names;
    for (const auto& port : decl->ports) {
      if (port.is_explicit_named && !port.name.empty()) {
        if (!explicit_names.insert(port.name).second) {
          diag_.Error(port.loc,
                      std::format("duplicate port name '.{}'", port.name));
        }
      }
    }
  }

  if (!decl->is_non_ansi_ports) {
    for (const auto& port : decl->ports) {
      if (!port.name.empty()) {
        if (!ansi_port_names_.insert(port.name).second) {
          diag_.Error(port.loc,
                      std::format("duplicate port name '{}'", port.name));
        }
      }
    }
  }

  for (const auto& port : decl->ports) {

    if (port.data_type.kind == DataTypeKind::kChandle) {
      diag_.Error(port.loc, "chandle cannot be used as a port type");
      continue;
    }
    if (port.data_type.kind == DataTypeKind::kVirtualInterface) {
      diag_.Error(port.loc,
                  "virtual interface cannot be used as a port type");
      continue;
    }

    if (decl->is_non_ansi_ports && !port.name.empty() &&
        !port.is_explicit_named && port.direction == Direction::kNone) {
      diag_.Error(port.loc,
                  std::format("port '{}' has no direction declaration in the "
                              "module body",
                              port.name));
    }

    if (decl->is_non_ansi_ports && !port.name.empty() &&
        port.direction != Direction::kNone) {
      if (port.data_type.kind != DataTypeKind::kImplicit) {
        non_ansi_complete_ports_.insert(port.name);
      } else {
        non_ansi_partial_ports_[port.name] =
            EvalTypeWidth(port.data_type, typedefs_, param_scope);
        // §23.2.2.1: remember a `signed` port direction declaration so the
        // matching net/variable declaration can be considered signed too.
        if (port.data_type.is_signed)
          non_ansi_signed_ports_.insert(port.name);
      }
    }

    if (port.default_value) {
      if (port.direction != Direction::kInput) {
        diag_.Error(port.loc,
                    std::format("default value on {} port '{}'; defaults are "
                                "only allowed on input ports",
                                port.direction == Direction::kOutput  ? "output"
                                : port.direction == Direction::kInout ? "inout"
                                                                     : "ref",
                                port.name));
      }
      if (decl->is_non_ansi_ports) {
        diag_.Error(port.loc,
                    std::format("default value on port '{}'; defaults are "
                                "only allowed with ANSI-style port "
                                "declarations",
                                port.name));
      }
      if (port.data_type.is_interconnect) {
        diag_.Error(port.loc,
                    std::format("default value on interconnect port '{}'",
                                port.name));
      }
      if (!port.unpacked_dims.empty() || !IsSingularType(port.data_type)) {
        diag_.Error(port.loc,
                    std::format("default value on non-singular port '{}'",
                                port.name));
      }
    }

    // §23.2.2.1: it is illegal to specify `signed` for a port declared as an
    // interconnect port. Interconnect is an untyped generic connection, so it
    // carries no signedness of its own.
    if (port.data_type.is_interconnect && port.data_type.is_signed) {
      diag_.Error(port.loc,
                  std::format("interconnect port '{}' shall not be declared "
                              "signed",
                              port.name));
    }

    bool port_is_var =
        !port.data_type.is_net && !port.data_type.is_interconnect;

    if (port.direction == Direction::kInout && port_is_var) {
      diag_.Error(port.loc,
                  std::format("variable data type is not permitted on "
                              "inout port '{}'",
                              port.name));
    }

    RtlirPort rp;
    rp.name = port.name;
    rp.direction = port.direction;
    rp.type_kind = port.data_type.kind;
    rp.width = EvalTypeWidth(port.data_type, typedefs_, param_scope);
    rp.is_signed = port.data_type.is_signed;
    rp.is_var = port_is_var;
    rp.is_interconnect = port.data_type.is_interconnect;
    rp.default_value = port.default_value;

    for (auto* dim : port.unpacked_dims) {
      if (!dim) continue;
      if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
        auto lv = ConstEvalInt(dim->lhs);
        auto rv = ConstEvalInt(dim->rhs);
        if (lv && rv) {
          rp.unpacked_dim_sizes.push_back(
              static_cast<uint32_t>(std::abs(*lv - *rv) + 1));
        }
      } else {
        auto sv = ConstEvalInt(dim);
        if (sv && *sv > 0)
          rp.unpacked_dim_sizes.push_back(static_cast<uint32_t>(*sv));
      }
    }
    rp.num_unpacked_dims =
        static_cast<uint32_t>(rp.unpacked_dim_sizes.size());

    if (port.is_interface_port) {
      rp.is_interface_port = true;
    } else if (port.direction == Direction::kNone &&
               port.data_type.kind == DataTypeKind::kNamed &&
               !port.data_type.type_name.empty()) {
      auto* ifc_decl = FindModule(port.data_type.type_name);
      if (ifc_decl && ifc_decl->decl_kind == ModuleDeclKind::kInterface) {
        rp.is_interface_port = true;
        rp.interface_type_name = port.data_type.type_name;
      }
    }

    mod->ports.push_back(rp);
  }
}

RtlirNet MakeImplicitPortNet(std::string_view name, uint32_t port_width,
                             bool port_is_signed, NetType default_nettype) {
  RtlirNet net;
  net.name = name;
  // §6.10: an implicit net assumed for a port expression takes the default net
  // type and the vector width of the port expression declaration.
  net.net_type = default_nettype;
  net.width = port_width == 0 ? 1 : port_width;
  // §23.2.2.1: nets connected to ports without an explicit net declaration are
  // unsigned unless the port itself is declared signed.
  net.is_signed = port_is_signed;
  return net;
}

uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod) {
  if (!lhs || lhs->kind != ExprKind::kIdentifier) return 0;
  for (const auto& v : mod->variables) {
    if (v.name == lhs->text) return v.width;
  }
  for (const auto& n : mod->nets) {
    if (n.name == lhs->text) return n.width;
  }
  for (const auto& p : mod->ports) {
    if (p.name == lhs->text) return p.width;
  }
  return 0;
}

RtlirProcessKind MapAlwaysKind(AlwaysKind ak) {
  switch (ak) {
    case AlwaysKind::kAlways:
      return RtlirProcessKind::kAlways;
    case AlwaysKind::kAlwaysComb:
      return RtlirProcessKind::kAlwaysComb;
    case AlwaysKind::kAlwaysFF:
      return RtlirProcessKind::kAlwaysFF;
    case AlwaysKind::kAlwaysLatch:
      return RtlirProcessKind::kAlwaysLatch;
  }
  return RtlirProcessKind::kAlwaysComb;
}

static bool StmtHasForkJoin(const Stmt* stmt) {
  if (!stmt) return false;
  if (stmt->kind == StmtKind::kFork) return true;
  for (const auto* s : stmt->stmts)
    if (StmtHasForkJoin(s)) return true;
  if (StmtHasForkJoin(stmt->then_branch)) return true;
  if (StmtHasForkJoin(stmt->else_branch)) return true;
  if (StmtHasForkJoin(stmt->body)) return true;
  if (StmtHasForkJoin(stmt->for_body)) return true;
  for (const auto& ci : stmt->case_items)
    if (StmtHasForkJoin(ci.body)) return true;
  return false;
}

static bool MayInferLatch(const Stmt* stmt);

static bool MayInferLatchCase(const Stmt* stmt) {
  bool has_default = false;
  for (const auto& ci : stmt->case_items)
    if (ci.is_default) {
      has_default = true;
      break;
    }
  if (!has_default) return true;
  for (const auto& ci : stmt->case_items)
    if (MayInferLatch(ci.body)) return true;
  return false;
}

static bool MayInferLatch(const Stmt* stmt) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kIf:
      if (!stmt->else_branch) return true;
      return MayInferLatch(stmt->then_branch) ||
             MayInferLatch(stmt->else_branch);
    case StmtKind::kCase:
      return MayInferLatchCase(stmt);
    case StmtKind::kBlock:
      for (const auto* s : stmt->stmts)
        if (MayInferLatch(s)) return true;
      return false;
    default:
      return false;
  }
}

static bool StmtHasTimingControl(const Stmt* stmt) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kTimingControl:
    case StmtKind::kDelay:
    case StmtKind::kEventControl:
    case StmtKind::kWait:
    case StmtKind::kWaitFork:
      return true;
    case StmtKind::kBlock:
      for (const auto* s : stmt->stmts)
        if (StmtHasTimingControl(s)) return true;
      return false;
    case StmtKind::kIf:
      return StmtHasTimingControl(stmt->then_branch) ||
             StmtHasTimingControl(stmt->else_branch);
    case StmtKind::kFor:
      return StmtHasTimingControl(stmt->for_body);
    case StmtKind::kWhile:
    case StmtKind::kDoWhile:
    case StmtKind::kForever:
    case StmtKind::kRepeat:
    case StmtKind::kForeach:
      return StmtHasTimingControl(stmt->body);
    case StmtKind::kFork:
      for (const auto* s : stmt->fork_stmts)
        if (StmtHasTimingControl(s)) return true;
      return false;
    default:
      return false;
  }
}

static void ValidateCombLatchProcess(ModuleItem* item, const RtlirProcess& proc,
                                     RtlirProcessKind kind, DiagEngine& diag) {
  if (kind != RtlirProcessKind::kAlwaysComb &&
      kind != RtlirProcessKind::kAlwaysLatch)
    return;
  if (StmtHasTimingControl(proc.body)) {
    const char* kw = (kind == RtlirProcessKind::kAlwaysComb) ? "always_comb"
                                                             : "always_latch";
    diag.Error(item->loc,
               std::format("{} shall not contain timing controls", kw));
  }
  if (StmtHasForkJoin(proc.body)) {
    const char* kw = (kind == RtlirProcessKind::kAlwaysComb) ? "always_comb"
                                                             : "always_latch";
    diag.Error(item->loc,
               std::format("{} shall not contain fork-join statements", kw));
  }
  if (kind == RtlirProcessKind::kAlwaysComb && MayInferLatch(proc.body)) {
    diag.Warning(item->loc,
                 "always_comb may infer latched behavior; "
                 "ensure all paths assign all outputs");
  }
  if (kind == RtlirProcessKind::kAlwaysLatch && !MayInferLatch(proc.body)) {
    diag.Warning(item->loc,
                 "always_latch does not infer latched behavior; "
                 "ensure incomplete assignments create intended latches");
  }
}

static void ValidateAlwaysFFProcess(ModuleItem* item, const RtlirProcess& proc,
                                    DiagEngine& diag) {
  if (item->sensitivity.empty()) {
    diag.Error(item->loc, "always_ff requires an event control");
  }
  if (StmtHasTimingControl(proc.body)) {
    diag.Error(item->loc,
               "always_ff shall not contain blocking timing controls");
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc, "always_ff shall not contain fork-join statements");
  }
  bool has_edge = false;
  for (const auto& ev : item->sensitivity) {
    if (ev.edge == Edge::kPosedge || ev.edge == Edge::kNegedge) {
      has_edge = true;
      break;
    }
  }
  if (!item->sensitivity.empty() && !has_edge) {
    diag.Warning(item->loc,
                 "always_ff has no edge-sensitive event; "
                 "may not represent sequential logic");
  }
}

static void ValidateFinalProcess(ModuleItem* item, const RtlirProcess& proc,
                                 DiagEngine& diag) {
  if (StmtHasTimingControl(proc.body)) {
    diag.Error(item->loc, "final procedure shall not contain timing controls");
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc,
               "final procedure shall not contain fork-join statements");
  }
}

void AddProcess(
    RtlirProcessKind kind, ModuleItem* item, RtlirModule* mod, Arena& arena,
    DiagEngine& diag,
    const std::unordered_map<std::string_view, const ModuleItem*>* func_map) {
  RtlirProcess proc;
  proc.kind = kind;
  proc.body = item->body;
  proc.sensitivity = item->sensitivity;
  proc.is_star_sensitivity = item->is_star_sensitivity;
  bool needs_infer = (kind == RtlirProcessKind::kAlwaysComb ||
                      kind == RtlirProcessKind::kAlwaysLatch);
  if (needs_infer && proc.sensitivity.empty()) {
    proc.sensitivity = InferSensitivity(proc.body, arena, func_map);
  }
  if (kind == RtlirProcessKind::kAlways && item->is_star_sensitivity &&
      proc.sensitivity.empty()) {
    proc.sensitivity =
        InferSensitivity(proc.body, arena, nullptr, false);
  }

  if (kind == RtlirProcessKind::kAlways && item->sensitivity.empty() &&
      !item->is_star_sensitivity && !StmtHasTimingControl(proc.body)) {
    diag.Warning(item->loc,
                 "always block has no timing control; may cause "
                 "a zero-delay loop");
  }
  ValidateCombLatchProcess(item, proc, kind, diag);
  if (kind == RtlirProcessKind::kAlwaysFF) {
    ValidateAlwaysFFProcess(item, proc, diag);
  }
  if (kind == RtlirProcessKind::kFinal) {
    ValidateFinalProcess(item, proc, diag);
  }

  proc.attrs = ResolveAttributes(item->attrs, diag);
  mod->processes.push_back(proc);
}

static void CollectStmtLhsPrefixes(const Stmt* stmt,
                                   std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    if (stmt->lhs) {
      std::string prefix = LongestStaticPrefix(stmt->lhs);
      if (!prefix.empty()) out.insert(std::move(prefix));
    }
  }
  for (const auto* s : stmt->stmts) CollectStmtLhsPrefixes(s, out);
  CollectStmtLhsPrefixes(stmt->then_branch, out);
  CollectStmtLhsPrefixes(stmt->else_branch, out);
  CollectStmtLhsPrefixes(stmt->body, out);
  CollectStmtLhsPrefixes(stmt->for_body, out);
  for (auto* fi : stmt->for_inits) CollectStmtLhsPrefixes(fi, out);
  for (auto* fs : stmt->for_steps) CollectStmtLhsPrefixes(fs, out);
  for (const auto& ci : stmt->case_items) CollectStmtLhsPrefixes(ci.body, out);
  for (const auto* s : stmt->fork_stmts) CollectStmtLhsPrefixes(s, out);
}

static void CollectCallNamesExpr(
    const Expr* expr, std::unordered_set<std::string_view>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty())
    out.insert(expr->callee);
  CollectCallNamesExpr(expr->lhs, out);
  CollectCallNamesExpr(expr->rhs, out);
  CollectCallNamesExpr(expr->condition, out);
  CollectCallNamesExpr(expr->true_expr, out);
  CollectCallNamesExpr(expr->false_expr, out);
  CollectCallNamesExpr(expr->base, out);
  CollectCallNamesExpr(expr->index, out);
  for (auto* arg : expr->args) CollectCallNamesExpr(arg, out);
  for (auto* elem : expr->elements) CollectCallNamesExpr(elem, out);
}

static void CollectCallNamesStmt(
    const Stmt* stmt, std::unordered_set<std::string_view>& out) {
  if (!stmt) return;
  CollectCallNamesExpr(stmt->expr, out);
  CollectCallNamesExpr(stmt->rhs, out);
  CollectCallNamesExpr(stmt->condition, out);
  CollectCallNamesExpr(stmt->for_cond, out);
  for (const auto* s : stmt->stmts) CollectCallNamesStmt(s, out);
  CollectCallNamesStmt(stmt->then_branch, out);
  CollectCallNamesStmt(stmt->else_branch, out);
  CollectCallNamesStmt(stmt->body, out);
  CollectCallNamesStmt(stmt->for_body, out);
  for (auto* fi : stmt->for_inits) CollectCallNamesStmt(fi, out);
  for (auto* fs : stmt->for_steps) CollectCallNamesStmt(fs, out);
  for (const auto& ci : stmt->case_items) CollectCallNamesStmt(ci.body, out);
  for (const auto* s : stmt->fork_stmts) CollectCallNamesStmt(s, out);
}

static void CollectFuncLhsPrefixes(
    const Stmt* body, const FuncMap& funcs,
    std::unordered_set<std::string>& out) {
  std::unordered_set<std::string_view> pending;
  CollectCallNamesStmt(body, pending);
  std::unordered_set<std::string_view> visited;
  while (!pending.empty()) {
    std::unordered_set<std::string_view> next;
    for (auto& name : pending) {
      if (visited.count(name)) continue;
      visited.insert(name);
      auto it = funcs.find(name);
      if (it == funcs.end()) continue;
      for (auto* s : it->second->func_body_stmts) {
        CollectStmtLhsPrefixes(s, out);
        CollectCallNamesStmt(s, next);
      }
    }
    pending = std::move(next);
  }
}

static bool PrefixesOverlap(const std::string& a, const std::string& b) {
  if (a == b) return true;
  if (a.size() < b.size())
    return b.compare(0, a.size(), a) == 0 &&
           (b[a.size()] == '.' || b[a.size()] == '[');
  if (b.size() < a.size())
    return a.compare(0, b.size(), b) == 0 &&
           (a[b.size()] == '.' || a[b.size()] == '[');
  return false;
}

struct ProcInfo {
  SourceLoc loc;
  std::unordered_set<std::string> lhs;
  ModuleItemKind kind;
};

static const char* ProcessKindLabel(ModuleItemKind k) {
  switch (k) {
    case ModuleItemKind::kAlwaysFFBlock:
      return "always_ff";
    case ModuleItemKind::kAlwaysLatchBlock:
      return "always_latch";
    default:
      return "always_comb";
  }
}

static void CollectProcessLhsInfo(
    const ModuleDecl* decl, std::vector<ProcInfo>& procs,
    std::unordered_set<std::string>& cont_assign_lhs,
    const FuncMap* func_map) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock) {
      ProcInfo info;
      info.loc = item->loc;
      info.kind = item->kind;
      CollectStmtLhsPrefixes(item->body, info.lhs);
      if (func_map && !func_map->empty())
        CollectFuncLhsPrefixes(item->body, *func_map, info.lhs);
      procs.push_back(std::move(info));
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_lhs) {
      std::string prefix = LongestStaticPrefix(item->assign_lhs);
      if (!prefix.empty()) cont_assign_lhs.insert(std::move(prefix));
    }
  }
}

static void CheckMultiProcDriver(const std::string& prefix, size_t i,
                                 const std::vector<ProcInfo>& procs,
                                 DiagEngine& diag) {
  for (size_t j = i + 1; j < procs.size(); ++j) {
    for (const auto& other : procs[j].lhs) {
      if (PrefixesOverlap(prefix, other)) {
        diag.Error(procs[j].loc,
                   std::format("variable '{}' driven by multiple "
                               "always_comb/always_latch/always_ff "
                               "processes",
                               prefix));
        break;
      }
    }
  }
}

static void CheckDriverConflicts(
    const std::vector<ProcInfo>& procs,
    const std::unordered_set<std::string>& cont_assign_lhs, DiagEngine& diag) {
  for (size_t i = 0; i < procs.size(); ++i) {
    for (const auto& var : procs[i].lhs) {
      for (const auto& ca : cont_assign_lhs) {
        if (PrefixesOverlap(var, ca)) {
          diag.Error(procs[i].loc,
                     std::format("variable '{}' driven by {} and "
                                 "continuous assignment",
                                 var, ProcessKindLabel(procs[i].kind)));
          break;
        }
      }
      CheckMultiProcDriver(var, i, procs, diag);
    }
  }
}

void Elaborator::CheckAlwaysCombMultiDriver(const ModuleDecl* decl,
                                            RtlirModule* ) {
  std::vector<ProcInfo> procs;
  std::unordered_set<std::string> cont_assign_lhs;
  CollectProcessLhsInfo(decl, procs, cont_assign_lhs, &func_decls_);
  CheckDriverConflicts(procs, cont_assign_lhs, diag_);
}

static void InferDynArraySize(const std::vector<Expr*>& dims, const Expr* init,
                              RtlirVariable& var) {
  if (dims.empty() || dims[0] != nullptr) return;
  if (var.is_queue || var.is_assoc) return;
  var.is_dynamic = true;
  if (init && !init->elements.empty()) {
    var.unpacked_size = static_cast<uint32_t>(init->elements.size());
  }
}

static bool TryParseQueueDim(const Expr* dim, RtlirVariable& var,
                             DiagEngine& diag, SourceLoc loc) {
  if (dim->kind != ExprKind::kIdentifier || dim->text != "$") return false;
  var.is_queue = true;
  if (dim->rhs) {
    auto max_val = ConstEvalInt(dim->rhs);
    if (max_val) {
      if (*max_val <= 0) {
        diag.Error(loc, "queue bound must be a positive integer");
      } else {
        var.queue_max_size = static_cast<int32_t>(*max_val + 1);
      }
    }
  }
  return true;
}

static bool TryParseRangeDim(const Expr* dim, RtlirVariable& var) {
  if (dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon)
    return false;
  auto lval = ConstEvalInt(dim->lhs);
  auto rval = ConstEvalInt(dim->rhs);
  if (!lval || !rval) return false;
  auto lo = std::min(*lval, *rval);
  auto hi = std::max(*lval, *rval);
  var.unpacked_lo = static_cast<uint32_t>(lo);
  var.unpacked_size = static_cast<uint32_t>(hi - lo + 1);
  var.is_descending = (*lval > *rval);
  return true;
}

static uint32_t AssocIndexWidth(std::string_view t) {
  if (t == "byte") return 8;
  if (t == "shortint") return 16;
  if (t == "longint") return 64;
  return 32;
}

static bool TryParseAssocDim(const Expr* dim, RtlirVariable& var) {
  if (dim->kind != ExprKind::kIdentifier) return false;
  auto t = dim->text;
  if (t == "string" || t == "int" || t == "integer" || t == "byte" ||
      t == "shortint" || t == "longint" || t == "*") {
    var.is_assoc = true;
    var.is_string_index = (t == "string");
    var.is_wildcard_index = (t == "*");
    var.assoc_index_width = AssocIndexWidth(t);
    // The built-in integral index types are signed; a wildcard index keeps an
    // unsigned, self-determined value (§7.8.4).
    var.is_index_signed = !var.is_wildcard_index;
    return true;
  }
  return false;
}

static bool IsUserDefinedType(
    std::string_view name, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  return typedefs.count(name) > 0 || class_names.count(name) > 0;
}

static void ComputeUnpackedDims(
    const std::vector<Expr*>& dims, RtlirVariable& var,
    const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names,
    DiagEngine& diag, SourceLoc loc) {
  if (dims.empty() || !dims[0]) return;
  auto* dim = dims[0];
  if (TryParseQueueDim(dim, var, diag, loc)) return;
  if (TryParseAssocDim(dim, var)) return;

  if (dim->kind == ExprKind::kIdentifier &&
      IsUserDefinedType(dim->text, typedefs, class_names)) {
    var.is_assoc = true;

    if (class_names.count(dim->text) > 0) {
      var.is_class_index = true;
      var.assoc_index_class_name = dim->text;
      var.assoc_index_width = 64;
    } else {

      auto it = typedefs.find(dim->text);
      if (it != typedefs.end()) {
        var.assoc_index_width = EvalTypeWidth(it->second, typedefs);
        // A typedef'd integral index follows the signedness of its underlying
        // type, so e.g. `bit signed [4:1]` orders signed and `bit [4:1]`
        // orders unsigned (§7.8.4).
        var.is_index_signed = IsSignedType(it->second, typedefs);
      }
    }
    return;
  }
  if (TryParseRangeDim(dim, var)) return;

  auto size_val = ConstEvalInt(dim);
  if (size_val) {
    if (*size_val <= 0) {
      diag.Error(loc,
                 "unpacked dimension size shall be a positive integer");
    } else {
      var.unpacked_size = static_cast<uint32_t>(*size_val);
    }
  }
}

bool Elaborator::ReconcilePartialPortSignedness(std::string_view name,
                                                bool decl_signed,
                                                RtlirModule* mod) {
  // §23.2.2.1: the signed attribute may sit on the port direction declaration,
  // on the corresponding net/variable declaration, or on both; if either is
  // signed, the other is considered signed too.
  bool effective = decl_signed || non_ansi_signed_ports_.count(name) != 0;
  if (effective) {
    non_ansi_signed_ports_.insert(name);
    for (auto& p : mod->ports) {
      if (p.name == name) p.is_signed = true;
    }
  }
  return effective;
}

void Elaborator::ElaborateNetDecl(ModuleItem* item, RtlirModule* mod) {
  if (ansi_port_names_.count(item->name)) {
    diag_.Error(item->loc,
                std::format("redeclaration of ANSI port '{}'", item->name));
  }

  if (non_ansi_complete_ports_.count(item->name)) {
    diag_.Error(
        item->loc,
        std::format("redeclaration of port '{}' that has a complete port "
                    "declaration",
                    item->name));
  }

  auto it = non_ansi_partial_ports_.find(item->name);
  if (it != non_ansi_partial_ports_.end()) {
    uint32_t net_width = EvalTypeWidth(item->data_type, typedefs_);
    if (net_width != it->second) {
      diag_.Error(
          item->loc,
          std::format(
              "vector range of net '{}' does not match its port declaration",
              item->name));
    }
  } else if (!declared_names_.insert(item->name).second) {
    diag_.Error(item->loc, std::format("redeclaration of '{}'", item->name));
  }
  net_names_.insert(item->name);
  var_types_[item->name] = item->data_type.kind;
  if (!item->data_type.packed_dim_left)
    scalar_var_names_.insert(item->name);
  else if (item->unpacked_dims.empty())
    packed_array_vars_.insert(item->name);
  RtlirNet net;
  net.name = ScopedName(item->name);

  if (item->data_type.is_interconnect) {
    net.net_type = NetType::kInterconnect;
    interconnect_names_.insert(item->name);
  } else {
    net.net_type = DataTypeToNetType(item->data_type.kind);
  }
  net.width = EvalTypeWidth(item->data_type, typedefs_);
  net.is_signed = IsSignedType(item->data_type, typedefs_);
  if (non_ansi_partial_ports_.count(item->name)) {
    net.is_signed =
        ReconcilePartialPortSignedness(item->name, net.is_signed, mod);
  }
  ValidatePackedDimRange(item->data_type, item->loc);

  if (!item->data_type.is_interconnect) {
    DataTypeKind k = item->data_type.kind;
    if (k != DataTypeKind::kStruct && k != DataTypeKind::kUnion &&
        k != DataTypeKind::kEnum && k != DataTypeKind::kNamed &&
        DataTypeToNetType(k) == NetType::kWire &&
        k != DataTypeKind::kWire && !Is4stateType(k)) {
      diag_.Error(item->loc, "net data type must be 4-state");
    }
  }

  if (item->data_type.charge_strength != 0 &&
      net.net_type != NetType::kTrireg) {
    diag_.Error(item->loc,
                "charge strength can only be used with trireg nets");
  }
  net.is_vectored = item->data_type.is_vectored;
  net.is_scalared = item->data_type.is_scalared;

  if ((item->data_type.is_vectored || item->data_type.is_scalared) &&
      net.width <= 1 && item->data_type.packed_dim_left == nullptr) {
    diag_.Error(item->loc,
                "vectored or scalared requires at least one packed dimension");
  }

  if (item->data_type.charge_strength != 0) {
    net.charge_strength =
        static_cast<Strength>(item->data_type.charge_strength);
  }

  if (net.net_type == NetType::kTrireg &&
      item->data_type.charge_strength == 0 &&
      unit_->has_default_trireg_strength) {
    net.trireg_capacitance = unit_->default_trireg_strength;
  }
  if (item->net_delay_decay) {
    net.decay_ticks =
        static_cast<uint64_t>(ConstEvalInt(item->net_delay_decay).value_or(0));
  } else if (net.net_type == NetType::kTrireg &&
             !unit_->default_decay_time_infinite) {

    net.decay_ticks = unit_->default_decay_time;
  }

  net.attrs = ResolveAttributes(item->attrs, diag_);
  mod->nets.push_back(net);

  if ((item->data_type.drive_strength0 != 0 ||
       item->data_type.drive_strength1 != 0) &&
      net.width > 1 && net.net_type != NetType::kSupply0 &&
      net.net_type != NetType::kSupply1) {
    diag_.Error(item->loc,
                "drive strength on continuous assignment applies only to "
                "scalar nets");
  }

  if (item->init_expr) {
    if (item->data_type.is_interconnect) {
      diag_.Error(
          item->loc,
          "interconnect net shall not have a net declaration assignment");
      return;
    }
    auto* lhs = arena_.Create<Expr>();
    lhs->kind = ExprKind::kIdentifier;
    lhs->text = item->name;
    lhs->range = item->init_expr->range;
    cont_assign_targets_.emplace(item->name, item->loc);
    RtlirContAssign ca;
    ca.lhs = lhs;
    ca.rhs = item->init_expr;
    ca.width = net.width;
    ca.drive_strength0 = item->data_type.drive_strength0;
    ca.drive_strength1 = item->data_type.drive_strength1;
    ca.delay = item->net_delay;
    ca.delay_fall = item->net_delay_fall;
    ca.delay_decay = item->net_delay_decay;
    mod->assigns.push_back(ca);
  }
}

static void SetEnumTypeInfo(const ModuleItem* item, RtlirVariable& var,
                            const TypedefMap& typedefs, Arena& arena) {
  if (item->data_type.kind == DataTypeKind::kEnum) {
    var.enum_type_name = item->name;
    var.dtype = &item->data_type;
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  auto it = typedefs.find(item->data_type.type_name);
  if (it != typedefs.end() && it->second.kind == DataTypeKind::kEnum) {
    var.enum_type_name = item->data_type.type_name;

    var.dtype = arena.Create<DataType>(it->second);
  }
}

void Elaborator::SetStructTypeInfo(const ModuleItem* item, RtlirVariable& var) {
  if (item->data_type.kind == DataTypeKind::kStruct ||
      item->data_type.kind == DataTypeKind::kUnion) {
    var.dtype = &item->data_type;
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  auto td = typedefs_.find(item->data_type.type_name);
  if (td == typedefs_.end()) return;
  if (td->second.kind != DataTypeKind::kStruct &&
      td->second.kind != DataTypeKind::kUnion) {
    return;
  }

  var.dtype = arena_.Create<DataType>(td->second);
}

void Elaborator::ValidateVarDeclTypes(ModuleItem* item) {

  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    class_var_names_.insert(item->name);
    class_var_types_[item->name] = item->data_type.type_name;

    if (item->data_type.type_params.empty()) {
      const auto* cls = FindClassDecl(item->data_type.type_name, unit_);
      if (cls && !cls->params.empty()) {
        for (const auto& [pname, pexpr] : cls->params) {
          if (!pexpr && !cls->type_param_names.count(pname)) {
            diag_.Error(item->loc,
                        std::format("parameterized class '{}' has no default "
                                    "specialization; parameter '{}' has no "
                                    "default value",
                                    cls->name, pname));
            break;
          }
        }
      }
    }

    if (item->data_type.type_name == "weak_reference" &&
        !item->data_type.type_params.empty()) {
      const auto& tp = item->data_type.type_params[0];
      if (tp.kind != DataTypeKind::kNamed || !class_names_.count(tp.type_name)) {
        diag_.Error(item->loc,
                    "weak_reference type parameter shall be a class type");
      }
    }
  }
  if (item->data_type.kind == DataTypeKind::kEnum) {
    ValidateEnumDecl(item->data_type, item->loc);
  }
  if (item->data_type.kind == DataTypeKind::kStruct ||
      item->data_type.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(item->data_type, item->loc);
    ValidateUnpackedStructWithUnionDefaults(item->data_type, item->loc);
    ValidateStructMemberDefaultsConstant(item->data_type, item->loc);
    ValidateVoidMembers(item->data_type, item->loc);
    ValidateRandQualifiers(item->data_type, item->loc);
    ValidatePackedDimRequiresPackedKeyword(item->data_type, item->loc);
    ValidatePackedStructMemberTypes(item->data_type, item->loc);
    ValidateChandleInUnion(item->data_type, item->loc);
    ValidateVirtualInterfaceInUnion(item->data_type, item->loc);
    ValidatePackedUnion(item->data_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->data_type, item->loc);
  ValidatePackedDimOnDisallowedType(item->data_type, item->loc);
  ValidateAssocIndexType(item);
}

void Elaborator::TrackVarArrayInfo(const ModuleItem* item,
                                   const RtlirVariable& var) {
  if (item->unpacked_dims.empty()) return;
  VarArrayInfo info{item->data_type.kind,
                    var.unpacked_size,
                    static_cast<uint32_t>(item->unpacked_dims.size()),
                    var.width,
                    var.is_signed,
                    var.is_4state,
                    var.is_dynamic,
                    var.is_assoc,
                    {},
                    {}};
  info.is_queue = var.is_queue;
  if (var.is_assoc && item->unpacked_dims[0] &&
      item->unpacked_dims[0]->kind == ExprKind::kIdentifier) {
    info.assoc_index_type = item->unpacked_dims[0]->text;
  }
  for (auto* dim : item->unpacked_dims) {
    if (!dim) continue;
    if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      auto lv = ConstEvalInt(dim->lhs);
      auto rv = ConstEvalInt(dim->rhs);
      if (lv && rv) {
        info.dim_sizes.push_back(
            static_cast<uint32_t>(std::abs(*lv - *rv) + 1));
      }
    } else {
      auto sv = ConstEvalInt(dim);
      if (sv && *sv > 0)
        info.dim_sizes.push_back(static_cast<uint32_t>(*sv));
    }
  }
  var_array_info_[item->name] = info;
}

namespace {

// §25.9: leftmost identifier of a (possibly hierarchical) reference, e.g.
// "top" for the path top.u.sig.
std::string_view ReferenceRootName(const Expr* e) {
  while (e != nullptr) {
    if (e->kind == ExprKind::kIdentifier) return e->text;
    if (e->lhs != nullptr) {
      e = e->lhs;
    } else if (e->base != nullptr) {
      e = e->base;
    } else {
      break;
    }
  }
  return {};
}

// §25.9: a reference is "external" to an interface when it is a hierarchical
// (dotted or scope-qualified) reference whose root name is not declared
// within the interface body.
bool ExprRefsOutsideInterface(
    const Expr* e, const std::unordered_set<std::string_view>& local) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    auto root = ReferenceRootName(e);
    if (!root.empty() && local.find(root) == local.end()) return true;
  }
  if (e->kind == ExprKind::kIdentifier && !e->scope_prefix.empty() &&
      local.find(e->text) == local.end()) {
    return true;
  }
  if (ExprRefsOutsideInterface(e->lhs, local)) return true;
  if (ExprRefsOutsideInterface(e->rhs, local)) return true;
  if (ExprRefsOutsideInterface(e->base, local)) return true;
  if (ExprRefsOutsideInterface(e->index, local)) return true;
  if (ExprRefsOutsideInterface(e->index_end, local)) return true;
  if (ExprRefsOutsideInterface(e->condition, local)) return true;
  if (ExprRefsOutsideInterface(e->true_expr, local)) return true;
  if (ExprRefsOutsideInterface(e->false_expr, local)) return true;
  if (ExprRefsOutsideInterface(e->repeat_count, local)) return true;
  for (const auto* a : e->args)
    if (ExprRefsOutsideInterface(a, local)) return true;
  for (const auto* el : e->elements)
    if (ExprRefsOutsideInterface(el, local)) return true;
  return false;
}

// §25.9: does the interface body reach outside itself through a hierarchical
// reference in a net/variable initializer or a continuous assignment?
bool InterfaceContainsExternalReference(const ModuleDecl* iface) {
  // §25.9: a port that references another interface also disqualifies the
  // interface from being used as a virtual interface type.
  for (const auto& p : iface->ports) {
    if (p.is_interface_port) return true;
  }
  std::unordered_set<std::string_view> local;
  for (const auto& p : iface->ports)
    if (!p.name.empty()) local.insert(p.name);
  for (const auto& param : iface->params)
    if (!param.first.empty()) local.insert(param.first);
  for (const auto* mp : iface->modports)
    if (mp && !mp->name.empty()) local.insert(mp->name);
  for (const auto* it : iface->items) {
    if (it == nullptr) continue;
    if (!it->name.empty()) local.insert(it->name);
    if (!it->inst_name.empty()) local.insert(it->inst_name);
  }
  for (const auto* it : iface->items) {
    if (it == nullptr) continue;
    if (ExprRefsOutsideInterface(it->init_expr, local)) return true;
    if (ExprRefsOutsideInterface(it->assign_lhs, local)) return true;
    if (ExprRefsOutsideInterface(it->assign_rhs, local)) return true;
  }
  return false;
}

}  // namespace

void Elaborator::ElaborateVarDecl(ModuleItem* item, RtlirModule* mod) {
  ResolveTypeRef(item, mod);

  ResolveParameterizedType(item->data_type);

  if (item->data_type.kind == DataTypeKind::kNamed &&
      nettype_names_.count(item->data_type.type_name)) {
    item->data_type.is_net = true;
    item->kind = ModuleItemKind::kNetDecl;
    nettype_net_names_.insert(item->name);
    ElaborateNetDecl(item, mod);

    auto& net = mod->nets.back();
    net.is_user_nettype = true;
    net.nettype_name = item->data_type.type_name;
    auto it = nettype_resolve_funcs_.find(item->data_type.type_name);
    if (it != nettype_resolve_funcs_.end()) {
      net.resolve_func = it->second;
    }
    return;
  }

  if (item->is_automatic) {
    diag_.Error(item->loc,
                "automatic lifetime is not allowed on module-level variables");
  }
  if (ansi_port_names_.count(item->name)) {
    diag_.Error(item->loc,
                std::format("redeclaration of ANSI port '{}'", item->name));
  }

  if (non_ansi_complete_ports_.count(item->name)) {
    diag_.Error(
        item->loc,
        std::format("redeclaration of port '{}' that has a complete port "
                    "declaration",
                    item->name));
  }

  auto partial_it = non_ansi_partial_ports_.find(item->name);
  if (partial_it != non_ansi_partial_ports_.end()) {
    uint32_t var_width = EvalTypeWidth(item->data_type, typedefs_);
    if (var_width != partial_it->second) {
      diag_.Error(
          item->loc,
          std::format("vector range of variable '{}' does not match its port "
                      "declaration",
                      item->name));
    }
  } else if (!declared_names_.insert(item->name).second) {
    diag_.Error(item->loc, std::format("redeclaration of '{}'", item->name));
  }

  if (item->data_type.is_const) {
    if (!item->init_expr) {
      diag_.Error(
          item->loc,
          std::format("const variable '{}' must be initialized", item->name));
    }
    const_names_.insert(item->name);
  }
  var_types_[item->name] = item->data_type.kind;
  if (!item->data_type.packed_dim_left)
    scalar_var_names_.insert(item->name);
  else if (item->unpacked_dims.empty())
    packed_array_vars_.insert(item->name);
  if (item->data_type.kind == DataTypeKind::kNamed)
    var_named_types_[item->name] = item->data_type.type_name;
  if (item->data_type.kind == DataTypeKind::kVirtualInterface) {
    auto iface_name = item->data_type.type_name;
    auto modport_name = item->data_type.modport_name;
    vi_var_interface_types_[item->name] = iface_name;
    vi_var_modports_[item->name] = modport_name;
    // §25.9: record explicit parameter overrides (when they evaluate to
    // constants) so a later assignment can confirm the actual parameter
    // values match the interface it is assigned from.
    if (!item->data_type.type_params.empty()) {
      std::vector<int64_t> values;
      bool all_const = true;
      for (const auto& tp : item->data_type.type_params) {
        if (tp.type_ref_expr == nullptr) {
          all_const = false;
          break;
        }
        auto v = ConstEvalInt(tp.type_ref_expr);
        if (!v) {
          all_const = false;
          break;
        }
        values.push_back(*v);
      }
      if (all_const) {
        vi_var_param_values_[item->name] = std::move(values);
      }
    }
    auto* iface_decl = FindModule(iface_name);
    if (!iface_decl ||
        iface_decl->decl_kind != ModuleDeclKind::kInterface) {
      diag_.Error(item->loc,
                  std::format("unknown interface '{}' in virtual interface "
                              "declaration",
                              iface_name));
    } else if (!modport_name.empty()) {
      bool found = false;
      for (const auto* mp : iface_decl->modports) {
        if (mp && mp->name == modport_name) {
          found = true;
          break;
        }
      }
      if (!found) {
        diag_.Error(item->loc,
                    std::format("modport '{}' not found in interface '{}'",
                                modport_name, iface_name));
      }
    }
    // §25.9: an interface containing hierarchical references to objects
    // outside its body (or ports that reference other interfaces) shall not
    // be used as the type of a virtual interface.
    if (iface_decl &&
        iface_decl->decl_kind == ModuleDeclKind::kInterface &&
        InterfaceContainsExternalReference(iface_decl)) {
      diag_.Error(item->loc,
                  std::format("interface '{}' contains references to objects "
                              "outside its body and cannot be used as a "
                              "virtual interface",
                              iface_name));
    }
  }
  RtlirVariable var;
  var.name = ScopedName(item->name);
  var.width = EvalTypeWidth(item->data_type, typedefs_);
  ValidatePackedDimRange(item->data_type, item->loc);
  var.is_4state = Is4stateType(item->data_type, typedefs_);
  var.is_event = (item->data_type.kind == DataTypeKind::kEvent);
  var.is_chandle = (item->data_type.kind == DataTypeKind::kChandle);
  var.is_string = (item->data_type.kind == DataTypeKind::kString);
  var.is_real = (item->data_type.kind == DataTypeKind::kReal ||
                 item->data_type.kind == DataTypeKind::kShortreal ||
                 item->data_type.kind == DataTypeKind::kRealtime);
  var.is_signed = IsSignedType(item->data_type, typedefs_);
  if (non_ansi_partial_ports_.count(item->name)) {
    var.is_signed =
        ReconcilePartialPortSignedness(item->name, var.is_signed, mod);
  }
  var.elem_type_kind = item->data_type.kind;
  var.init_expr = item->init_expr;

  if (item->init_expr) {
    var_init_names_.insert(item->name);
  }

  SetStructTypeInfo(item, var);

  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    var.class_type_name = item->data_type.type_name;
  }

  SetEnumTypeInfo(item, var, typedefs_, arena_);

  ComputeUnpackedDims(item->unpacked_dims, var, typedefs_, class_names_,
                      diag_, item->loc);
  ValidateUnpackedDimRange(item->unpacked_dims, item->loc);
  InferDynArraySize(item->unpacked_dims, item->init_expr, var);

  TrackVarArrayInfo(item, var);

  var.attrs = ResolveAttributes(item->attrs, diag_);
  mod->variables.push_back(var);
  ValidateArrayInitPattern(item);
  ValidateStructInitPattern(item);

  ValidateVarDeclTypes(item);
  TrackEnumVariable(item);
}

static bool IsBindTargetScope(std::string_view target,
                              const CompilationUnit* unit) {
  if (target.find('.') != std::string_view::npos) return false;
  for (auto* m : unit->modules)
    if (m->name == target) return true;
  for (auto* i : unit->interfaces)
    if (i->name == target) return true;
  for (auto* c : unit->checkers)
    if (c->name == target) return true;
  for (auto* p : unit->programs)
    if (p->name == target) return true;
  return false;
}

static std::unordered_set<std::string_view> CollectDeclaredNames(
    const RtlirModule* mod) {
  std::unordered_set<std::string_view> names;
  for (const auto& v : mod->variables) names.insert(v.name);
  for (const auto& n : mod->nets) names.insert(n.name);
  for (const auto& p : mod->ports) names.insert(p.name);
  for (const auto& c : mod->children) {
    if (!c.inst_name.empty()) names.insert(c.inst_name);
  }
  return names;
}

void Elaborator::ApplyBindDirectives(RtlirModule* top) {
  if (!top) return;
  std::vector<BindDirective*> binds;
  for (auto* bd : unit_->bind_directives) binds.push_back(bd);
  for (auto* m : unit_->modules)
    for (auto* bd : m->bind_directives) binds.push_back(bd);
  for (auto* i : unit_->interfaces)
    for (auto* bd : i->bind_directives) binds.push_back(bd);
  for (auto* p : unit_->programs)
    for (auto* bd : p->bind_directives) binds.push_back(bd);
  if (binds.empty()) return;
  std::unordered_set<RtlirModule*> visited;
  std::unordered_set<BindDirective*> applied;
  WalkForBind(top, std::string(top->name), binds, false,
              visited, applied);

  // §23.11: the bind_target_scope shall be a module or an interface, and a
  // bind_target_instance shall be an instance of a module or an interface. A
  // target naming a known scope is honored designwide even when that scope is
  // never instantiated, but a target that resolves to neither a known scope
  // nor any instance in the hierarchy denotes nothing bindable and is an error.
  for (auto* bd : binds) {
    if (applied.count(bd)) continue;
    if (IsBindTargetScope(bd->target, unit_)) continue;
    diag_.Error(bd->loc,
                std::format("bind target '{}' is neither a module or interface "
                            "scope nor an instance",
                            bd->target));
  }
}

void Elaborator::WalkForBind(RtlirModule* mod, const std::string& hier_path,
                             const std::vector<BindDirective*>& binds,
                             bool under_bind,
                             std::unordered_set<RtlirModule*>& visited,
                             std::unordered_set<BindDirective*>& applied) {
  if (!mod) return;
  if (!visited.insert(mod).second) return;

  for (auto* bd : binds) {
    bool applies = false;
    bool has_instances = !bd->target_instances.empty();
    bool is_scope = IsBindTargetScope(bd->target, unit_);
    if (is_scope && !has_instances) {

      if (mod->name == bd->target) applies = true;
    } else if (is_scope && has_instances) {

      if (mod->name == bd->target) {
        for (auto inst_path : bd->target_instances) {
          if (hier_path == inst_path) {
            applies = true;
            break;
          }
        }
      }
    } else {

      if (hier_path == bd->target) applies = true;
    }
    if (!applies) continue;
    // The target resolved to a real scope or instance, so it is bindable even
    // if elaboration of the instantiation later reports a different error.
    applied.insert(bd);
    if (under_bind) {
      diag_.Error(bd->loc,
                  "bind target shall not be a scope created by a bind");
      continue;
    }
    ApplyBindInstance(bd, mod);
  }

  size_t n = mod->children.size();
  for (size_t i = 0; i < n; ++i) {
    auto& c = mod->children[i];
    if (!c.resolved) continue;
    bool child_under_bind = under_bind || c.is_bound;
    std::string child_path = hier_path;
    child_path.push_back('.');
    child_path.append(c.inst_name.data(), c.inst_name.size());
    WalkForBind(c.resolved, child_path, binds, child_under_bind, visited,
                applied);
  }
}

void Elaborator::ApplyBindInstance(BindDirective* bd, RtlirModule* target) {
  auto* item = bd->instantiation;
  if (!item) return;

  auto* target_decl = FindModule(target->name);
  if (target_decl && target_decl->decl_kind == ModuleDeclKind::kInterface) {
    auto* bound_decl = FindModule(item->inst_module);
    if (bound_decl && bound_decl->decl_kind != ModuleDeclKind::kInterface &&
        bound_decl->decl_kind != ModuleDeclKind::kChecker) {
      diag_.Error(bd->loc,
                  std::format("cannot bind non-interface/non-checker '{}' "
                              "into interface '{}'",
                              item->inst_module, target->name));
      return;
    }
  }

  auto declared = CollectDeclaredNames(target);
  if (!item->inst_name.empty() && declared.count(item->inst_name)) {
    diag_.Error(bd->loc, std::format("bind instance name '{}' clashes with "
                                     "existing name in target scope '{}'",
                                     item->inst_name, target->name));
    return;
  }

  auto* child_decl = FindModule(item->inst_module);
  if (!child_decl) {
    diag_.Error(bd->loc,
                std::format("bind refers to unknown module '{}'",
                            item->inst_module));
    return;
  }

  for (const auto& [pname, conn_expr] : item->inst_ports) {
    if (!conn_expr || conn_expr->kind != ExprKind::kIdentifier) continue;
    auto name = conn_expr->text;
    bool found = false;
    for (const auto& v : target->variables) {
      if (v.name == name) { found = true; break; }
    }
    if (!found) {
      for (const auto& n : target->nets) {
        if (n.name == name) { found = true; break; }
      }
    }
    if (!found) {
      for (const auto& p : target->ports) {
        if (p.name == name) { found = true; break; }
      }
    }
    if (!found) {
      diag_.Error(bd->loc,
                  std::format("bind port connection '{}' references "
                              "undeclared signal '{}' in target scope '{}'",
                              pname, name, target->name));
      return;
    }
  }

  ParamList empty_params;
  auto* resolved = ElaborateModule(child_decl, empty_params);
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;
  inst.resolved = resolved;
  inst.is_bound = true;

  if (resolved) {
    const auto& child_ports = resolved->ports;
    const bool is_ordered =
        !item->inst_ports.empty() && item->inst_ports[0].first.empty();
    for (size_t i = 0; i < item->inst_ports.size(); ++i) {
      auto& [port_name, conn_expr] = item->inst_ports[i];
      RtlirPortBinding binding;
      binding.connection = conn_expr;
      auto it = child_ports.end();
      if (is_ordered) {
        if (i < child_ports.size()) {
          it = child_ports.begin() + static_cast<ptrdiff_t>(i);
          binding.port_name = it->name;
        }
      } else {
        binding.port_name = port_name;
        it = std::find_if(
            child_ports.begin(), child_ports.end(),
            [&](const RtlirPort& p) { return p.name == port_name; });
      }
      if (it != child_ports.end()) {
        binding.direction = it->direction;
        binding.width = it->width;
      } else {
        binding.direction = Direction::kInput;
        binding.width = 1;
      }
      inst.port_bindings.push_back(binding);
    }
  }

  target->children.push_back(inst);
}

namespace {

struct ExportKey {
  std::string_view iface_inst;
  std::string_view modport;
  std::string_view name;
  bool operator==(const ExportKey& o) const {
    return iface_inst == o.iface_inst && modport == o.modport && name == o.name;
  }
};

struct ExportKeyHash {
  size_t operator()(const ExportKey& k) const {
    std::hash<std::string_view> h;
    return h(k.iface_inst) ^ (h(k.modport) << 1) ^ (h(k.name) << 2);
  }
};

struct ExportSite {
  std::string_view child_inst;
  bool is_task = false;
  SourceLoc loc;
};

const ModportDecl* FindModportInInterface(const ModuleDecl* iface,
                                          std::string_view name) {
  for (const auto* mp : iface->modports) {
    if (mp->name == name) return mp;
  }
  return nullptr;
}

const ModuleItem* FindInterfaceExternPrototype(const ModuleDecl* iface,
                                               std::string_view name) {
  for (const auto* item : iface->items) {
    if (!item->is_extern) continue;
    if (item->kind != ModuleItemKind::kTaskDecl &&
        item->kind != ModuleItemKind::kFunctionDecl)
      continue;
    if (item->name == name) return item;
  }
  return nullptr;
}

const ModuleItem* FindOutOfBlockBodyInChild(const ModuleDecl* child,
                                            std::string_view iface_port_name,
                                            std::string_view method_name) {
  for (const auto* item : child->items) {
    if (item->kind != ModuleItemKind::kTaskDecl &&
        item->kind != ModuleItemKind::kFunctionDecl)
      continue;
    if (item->method_class == iface_port_name && item->name == method_name)
      return item;
  }
  return nullptr;
}

// §25.7: when a modport exports a subroutine using a full prototype, the
// definition supplied by the connected module shall match that prototype
// exactly — same kind (task vs function), the same argument types and
// directions, and, for a function, the same return type.
bool ExportPrototypeMatchesBody(const ModuleItem* proto,
                                const ModuleItem* body) {
  if (proto->kind != body->kind) return false;
  if (proto->func_args.size() != body->func_args.size()) return false;
  for (size_t i = 0; i < proto->func_args.size(); ++i) {
    if (!TypesMatch(proto->func_args[i].data_type,
                    body->func_args[i].data_type))
      return false;
    if (proto->func_args[i].direction != body->func_args[i].direction)
      return false;
  }
  // A modport function prototype keeps its return type in `data_type`, while an
  // out-of-block body keeps it in `return_type`; compare the matching fields.
  if (proto->kind == ModuleItemKind::kFunctionDecl &&
      !TypesMatch(proto->data_type, body->return_type))
    return false;
  return true;
}

}

void Elaborator::ValidateModportExportConflicts(RtlirModule* top) {
  if (!top) return;
  std::unordered_set<RtlirModule*> visited;
  WalkForExportConflicts(top, visited);
}

void Elaborator::WalkForExportConflicts(
    RtlirModule* mod, std::unordered_set<RtlirModule*>& visited) {
  if (!mod) return;
  if (!visited.insert(mod).second) return;

  std::unordered_map<std::string_view, std::string_view>
      iface_inst_to_type;
  for (const auto& c : mod->children) {
    if (auto* cd = FindModule(c.module_name);
        cd && cd->decl_kind == ModuleDeclKind::kInterface) {
      iface_inst_to_type[c.inst_name] = c.module_name;
    }
  }

  std::unordered_map<ExportKey, std::vector<ExportSite>, ExportKeyHash> buckets;

  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    auto* child_decl = FindModule(child.module_name);
    if (!child_decl) continue;
    if (child_decl->decl_kind == ModuleDeclKind::kInterface) continue;

    for (const auto& binding : child.port_bindings) {
      if (!binding.connection) continue;
      const auto* conn = binding.connection;

      std::string_view iface_inst_name;
      std::string_view modport_name;
      if (conn->kind == ExprKind::kIdentifier) {
        iface_inst_name = conn->text;
      } else if (conn->kind == ExprKind::kMemberAccess && conn->lhs &&
                 conn->lhs->kind == ExprKind::kIdentifier && conn->rhs &&
                 conn->rhs->kind == ExprKind::kIdentifier) {
        iface_inst_name = conn->lhs->text;
        modport_name = conn->rhs->text;
      } else {
        continue;
      }

      auto it = iface_inst_to_type.find(iface_inst_name);
      if (it == iface_inst_to_type.end()) continue;

      auto* iface_decl = FindModule(it->second);
      if (!iface_decl) continue;

      auto collect_exports =
          [&](const std::vector<ModportPort>& mp_ports) {
            for (const auto& pp : mp_ports) {
              if (!pp.is_export) continue;
              if (pp.name.empty()) continue;
              const auto* body = FindOutOfBlockBodyInChild(
                  child_decl, binding.port_name, pp.name);
              if (!body) continue;
              // §25.7: an export written as a full prototype pins the signature
              // the defining module must provide; a definition that does not
              // match it exactly is an elaboration error.
              if (pp.prototype &&
                  !ExportPrototypeMatchesBody(pp.prototype, body)) {
                diag_.Error(
                    body->loc,
                    std::format(
                        "definition of exported subroutine '{}' in module '{}' "
                        "does not match the prototype declared in the modport",
                        pp.name, child.module_name));
              }
              ExportKey key{iface_inst_name, modport_name, pp.name};
              ExportSite site;
              site.child_inst = child.inst_name;
              site.is_task = body->kind == ModuleItemKind::kTaskDecl;
              site.loc = body->loc;
              buckets[key].push_back(site);
            }
          };

      if (!modport_name.empty()) {
        const auto* mp = FindModportInInterface(iface_decl, modport_name);
        if (!mp) continue;
        collect_exports(mp->ports);
      } else {
        for (const auto* mp : iface_decl->modports) {
          collect_exports(mp->ports);
        }
      }
    }
  }

  for (const auto& [key, sites] : buckets) {
    if (sites.size() < 2) continue;

    auto type_it = iface_inst_to_type.find(key.iface_inst);
    if (type_it == iface_inst_to_type.end()) continue;
    auto* iface_decl = FindModule(type_it->second);
    if (!iface_decl) continue;

    const ModuleItem* prototype =
        FindInterfaceExternPrototype(iface_decl, key.name);
    bool is_task_export = sites[0].is_task;
    bool is_forkjoin_task = prototype && prototype->is_extern &&
                            prototype->is_forkjoin &&
                            prototype->kind == ModuleItemKind::kTaskDecl;

    if (is_task_export && is_forkjoin_task) continue;

    if (!is_task_export) {
      diag_.Error(
          sites[0].loc,
          std::format("function '{}' exported by more than one module "
                      "connected to interface instance '{}' (§25.7.4: "
                      "multiple export of functions is not allowed)",
                      key.name, key.iface_inst));
    } else {
      diag_.Error(
          sites[0].loc,
          std::format("task '{}' exported by more than one module connected "
                      "to interface instance '{}' (§25.7.4: declare the task "
                      "as `extern forkjoin` in the interface to allow "
                      "multiple exports)",
                      key.name, key.iface_inst));
    }
  }

  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    WalkForExportConflicts(child.resolved, visited);
  }
}

}
