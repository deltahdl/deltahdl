#include <algorithm>
#include <cmath>
#include <format>
#include <functional>
#include <map>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static ResolvedAttribute EvalAttribute(const Attribute& attr,
                                       const ScopeMap& scope) {
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
    // §A.9.1/§5.12: an attribute value is a constant expression that may
    // reference module parameters, so evaluate it against the param scope.
    ra.resolved_value = ConstEvalInt(attr.value, scope);
  }
  return ra;
}

std::vector<ResolvedAttribute> ResolveAttributes(
    const std::vector<Attribute>& attrs, DiagEngine& diag,
    const ScopeMap& scope) {
  std::vector<ResolvedAttribute> result;
  for (const auto& attr : attrs) {
    auto ra = EvalAttribute(attr, scope);
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

namespace {

void ValidateNameSpaceDefinitions(const CompilationUnit* unit,
                                  DiagEngine& diag) {
  std::map<std::pair<std::string_view, std::string_view>, SourceRange>
      def_names;
  auto check_def = [&](std::string_view library, std::string_view name,
                       SourceRange range) {
    auto [it, inserted] = def_names.try_emplace({library, name}, range);
    if (!inserted) {
      diag.Error(range.start,
                 std::format("duplicate definition of '{}'", name));
    }
  };
  // §23.5: an extern module declaration declares a module's ports without
  // defining the module itself, so it is a prototype rather than a definition
  // and does not participate in the duplicate-definition check. The prototype
  // is matched against its actual definition in elaborator_resolve.
  for (auto* m : unit->modules)
    if (!m->is_extern) check_def(m->library, m->name, m->range);
  for (auto* p : unit->programs) check_def(p->library, p->name, p->range);
  for (auto* i : unit->interfaces) check_def(i->library, i->name, i->range);
  for (auto* u : unit->udps) check_def(u->library, u->name, u->range);

  for (auto* cfg : unit->configs)
    check_def(cfg->library, cfg->name, cfg->range);
}

void ValidateNameSpacePackages(const CompilationUnit* unit, DiagEngine& diag) {
  std::unordered_set<std::string_view> pkg_names;
  for (auto* pkg : unit->packages) {
    if (!pkg_names.insert(pkg->name).second) {
      diag.Error(pkg->range.start,
                 std::format("duplicate package '{}'", pkg->name));
    }

    if (pkg->name == "std") {
      diag.Error(pkg->range.start,
                 "'std' is reserved for the built-in package and cannot "
                 "be declared by the user");
    }
  }
}

void ValidateNameSpaceCompilationUnit(const CompilationUnit* unit,
                                      DiagEngine& diag) {
  // The library a declaration belongs to is part of what identifies it.
  // §3.13(c) unifies these names within one compilation-unit scope, and §33.2.1
  // has a library be a collection of cells whose names are that library's, so
  // two libraries each holding a cell of one name hold two design elements
  // rather than one name declared twice. A declaration no library map reached
  // carries no library, which is the ordinary compilation the subclause
  // describes, and there the key is the name alone.
  std::map<std::pair<std::string_view, std::string_view>, SourceLoc>
      cu_scope_names;
  auto check_cu = [&](std::string_view library, std::string_view name,
                      SourceLoc loc) {
    if (name.empty()) return;
    auto [it, inserted] = cu_scope_names.try_emplace({library, name}, loc);
    if (!inserted) {
      diag.Error(
          loc,
          std::format("redeclaration of '{}' in compilation-unit scope", name));
    }
  };
  for (auto* item : unit->cu_items) {
    if (item->kind == ModuleItemKind::kImportDecl ||
        item->kind == ModuleItemKind::kExportDecl)
      continue;
    if (item->from_anonymous_program) continue;
    // §6.18: a forward typedef (e.g. `typedef interface class IC;`, carried as
    // a kTypedef with an implicit aliased type) is a forward declaration, not a
    // definition; it does not redeclare the eventual class or typedef of the
    // same name. An unresolved forward typedef is reported separately.
    if (item->kind == ModuleItemKind::kTypedef &&
        item->typedef_type.kind == DataTypeKind::kImplicit)
      continue;
    check_cu({}, item->name, item->loc);
  }
  for (auto* cls : unit->classes) check_cu({}, cls->name, cls->range.start);
  // §3.2 counts a checker a design element and §33.2.1 counts a design element
  // a cell, so a checker is one of the things a library holds under its own
  // name.
  for (auto* chk : unit->checkers) {
    check_cu(chk->library, chk->name, chk->range.start);
  }
}

}  // namespace

void Elaborator::ValidateNameSpaces() {
  ValidateNameSpaceDefinitions(unit_, diag_);
  ValidateNameSpacePackages(unit_, diag_);
  ValidateNameSpaceCompilationUnit(unit_, diag_);
}

std::unordered_set<std::string_view> NonConfigCellNames(
    const CompilationUnit* unit) {
  std::unordered_set<std::string_view> names;
  for (auto* m : unit->modules) names.insert(m->name);
  for (auto* u : unit->udps) names.insert(u->name);
  for (auto* i : unit->interfaces) names.insert(i->name);
  for (auto* p : unit->programs) names.insert(p->name);
  for (auto* c : unit->checkers) names.insert(c->name);
  return names;
}

void Elaborator::ValidateConfigDesignStatements() {
  std::unordered_set<std::string_view> config_names;
  for (auto* cfg : unit_->configs) config_names.insert(cfg->name);

  // A design cell is allowed to share its name with a config; when a cell of
  // that name also exists, the design statement denotes the cell rather than
  // the like-named config. A name that resolves only to a config is therefore
  // the case that must be rejected as a design target.
  std::unordered_set<std::string_view> cell_names = NonConfigCellNames(unit_);

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

namespace {

void ValidateConfigInstanceClausesOne(const ConfigDecl* cfg, DiagEngine& diag) {
  if (cfg->design_cells.empty()) return;
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
      diag.Error(cfg->range.start,
                 std::format("instance path '{}' in config '{}' does not start "
                             "at a top-level cell of the config's design "
                             "statement",
                             rule->inst_path, cfg->name));
    }
  }
}

}  // namespace

void Elaborator::ValidateConfigInstanceClauses() {
  for (auto* cfg : unit_->configs) {
    ValidateConfigInstanceClausesOne(cfg, diag_);
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

namespace {

// The instance paths this config hands over to another config. Which use
// clauses name a config is §33.2.1's question, not a matter of the ':config'
// extension being written: a use clause whose name reaches no cell other than
// the config of that name names the config with the extension left off.
std::vector<std::string_view> CollectDelegatedSubhierarchies(
    const ConfigDecl* cfg, const CompilationUnit* unit) {
  std::vector<std::string_view> delegated;
  for (auto* rule : cfg->rules) {
    if (rule->kind == ConfigRuleKind::kInstance &&
        UseClauseNamesConfig(rule, cfg, unit)) {
      delegated.push_back(rule->inst_path);
    }
  }
  return delegated;
}

void ValidateConfigHierarchicalRulesOne(const ConfigDecl* cfg,
                                        const CompilationUnit* unit,
                                        DiagEngine& diag) {
  std::vector<std::string_view> delegated =
      CollectDelegatedSubhierarchies(cfg, unit);

  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    auto path = rule->inst_path;
    for (auto root : delegated) {
      if (path == root) continue;
      if (path.size() > root.size() + 1 && path.starts_with(root) &&
          path[root.size()] == '.') {
        diag.Error(cfg->range.start,
                   std::format("instance '{}' in config '{}' lies within "
                               "subhierarchy '{}' that is delegated to another "
                               "config",
                               path, cfg->name, root));
        break;
      }
    }
  }
}

}  // namespace

void Elaborator::ValidateConfigHierarchicalRules() {
  for (auto* cfg : unit_->configs) {
    ValidateConfigHierarchicalRulesOne(cfg, unit_, diag_);
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
bool WalkExprAnyChildren(const Expr* expr, Visitor&& v);

template <typename Visitor>
bool WalkExprAny(const Expr* expr, Visitor&& v) {
  if (!expr) return false;
  if (v(expr)) return true;
  return WalkExprAnyChildren(expr, v);
}

template <typename Visitor>
bool WalkExprAnyChildren(const Expr* expr, Visitor&& v) {
  const Expr* const kScalarChildren[] = {
      expr->lhs,          expr->rhs,      expr->condition, expr->true_expr,
      expr->false_expr,   expr->base,     expr->index,     expr->index_end,
      expr->repeat_count, expr->with_expr};
  for (const Expr* child : kScalarChildren) {
    if (WalkExprAny(child, v)) return true;
  }
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

namespace {

bool IsPureTermTree(const Expr* e) {
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
}

void CheckParamOverrideSelectIndices(
    const ConfigDecl* cfg, std::string_view pname, const Expr* expr,
    const std::unordered_set<std::string_view>& lp_names, DiagEngine& diag) {
  auto check_index = [&](const Expr* idx) {
    WalkExprAny(idx, [&](const Expr* sub) {
      if (sub->kind == ExprKind::kIdentifier &&
          lp_names.count(sub->text) == 0) {
        diag.Error(cfg->range.start,
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
}

void ValidateOneParamOverride(
    const ConfigDecl* cfg, std::string_view pname, const Expr* expr,
    const std::unordered_set<std::string_view>& lp_names, DiagEngine& diag) {
  bool has_hier = WalkExprAny(
      expr, [](const Expr* e) { return e->kind == ExprKind::kMemberAccess; });

  if (has_hier && !IsPureTermTree(expr)) {
    diag.Error(cfg->range.start,
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
    diag.Error(cfg->range.start,
               std::format("config '{}' override of parameter '{}' uses a "
                           "hierarchical reference that traverses an array of "
                           "instances",
                           cfg->name, pname));
  }

  CheckParamOverrideSelectIndices(cfg, pname, expr, lp_names, diag);

  bool has_user_call = WalkExprAny(
      expr, [](const Expr* e) { return e->kind == ExprKind::kCall; });
  if (has_user_call) {
    diag.Error(cfg->range.start,
               std::format("config '{}' override of parameter '{}' calls a "
                           "user-defined function; only built-in constant "
                           "functions are permitted",
                           cfg->name, pname));
  }
}

}  // namespace

void Elaborator::ValidateConfigParamOverrides() {
  for (auto* cfg : unit_->configs) {
    std::unordered_set<std::string_view> lp_names;
    for (const auto& [name, _] : cfg->local_params) lp_names.insert(name);

    for (auto* rule : cfg->rules) {
      for (const auto& [pname, expr] : rule->use_params) {
        if (!expr) continue;
        ValidateOneParamOverride(cfg, pname, expr, lp_names, diag_);
      }
    }
  }
}

namespace {

void CheckAnonymousProgramScope(const std::vector<ModuleItem*>& items,
                                DiagEngine& diag) {
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
      diag.Error(item->loc,
                 std::format(
                     "'{}' declared in anonymous program collides with name in "
                     "surrounding package or compilation-unit scope",
                     item->name));
    }
  }
}

}  // namespace

void Elaborator::ValidateAnonymousProgramNameSharing() {
  CheckAnonymousProgramScope(unit_->cu_items, diag_);
  for (const auto* pkg : unit_->packages) {
    CheckAnonymousProgramScope(pkg->items, diag_);
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

}  // namespace delta
