#include "elaborator/elaborator.h"

#include <algorithm>
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

// Defined in elaborator_gates.cpp.
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

// §5.12: Evaluate a single AST attribute into a ResolvedAttribute.
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

// §5.12: Resolve AST attributes into RTLIR ResolvedAttributes.
// Deduplicates (last wins) and evaluates constant expressions.
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
  // §3.13(a): Definitions name space — module, primitive, program, interface
  // names must be unique across all design elements.  §33.6.1's example
  // depends on the same cell name appearing in different libraries (e.g.,
  // `m` lives in rtlLib, aLib, and gateLib simultaneously); the uniqueness
  // key therefore pairs the library tag with the name so cross-library
  // duplicates coexist while same-library duplicates still error.
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
  for (auto* c : unit_->checkers) check_def(c->library, c->name, c->range);
  for (auto* u : unit_->udps) check_def(u->library, u->name, u->range);
  // §33.2: a config is a design element peer to modules, so its name shares
  // the same definitions space and must be unique against every other entry.
  for (auto* cfg : unit_->configs) check_def(cfg->library, cfg->name, cfg->range);

  // §3.13(b): Package name space — package names must be unique.
  std::unordered_set<std::string_view> pkg_names;
  for (auto* pkg : unit_->packages) {
    if (!pkg_names.insert(pkg->name).second) {
      diag_.Error(pkg->range.start,
                  std::format("duplicate package '{}'", pkg->name));
    }
    // §26.7: the name std is reserved for the built-in package; users
    // cannot insert additional declarations into it.
    if (pkg->name == "std") {
      diag_.Error(pkg->range.start,
                  "'std' is reserved for the built-in package and cannot "
                  "be declared by the user");
    }
  }
}

void Elaborator::ValidateConfigDesignStatements() {
  std::unordered_set<std::string_view> config_names;
  for (auto* cfg : unit_->configs) config_names.insert(cfg->name);

  for (auto* cfg : unit_->configs) {
    for (auto& [lib, cell] : cfg->design_cells) {
      // §33.4.1.1: a design cell cannot be a configuration.
      if (config_names.contains(cell)) {
        diag_.Error(
            cfg->range.start,
            std::format("config '{}' design statement names configuration "
                        "'{}'; design cells must not be configs",
                        cfg->name, cell));
      }
      // §33.4.1.1: an omitted library identifier resolves to the
      // library that contains this config (set by §33.3.3 tagging).
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
      // §33.4.1.4: distinguish use-expansion from liblist-expansion by
      // checking whether any use-clause field was populated; an empty
      // liblist with `liblist` keyword still falls through here, but
      // the rule is still ill-formed under §33.4.1.4 either way.
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

void Elaborator::ValidateConfigHierarchicalRules() {
  for (auto* cfg : unit_->configs) {
    // Collect the inst paths that delegate a subhierarchy to another
    // config (they carry the `:config` suffix).
    std::vector<std::string_view> delegated;
    for (auto* rule : cfg->rules) {
      if (rule->kind == ConfigRuleKind::kInstance && rule->use_config) {
        delegated.push_back(rule->inst_path);
      }
    }
    // Each instance rule's path must not lie strictly within any
    // delegated subhierarchy.  An exact match against the delegating
    // path itself is fine; anything that goes one level deeper is the
    // §33.4.2 error.
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

// Walk `expr`'s children with a visitor that returns true to short-circuit.
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
    // Names that are legal as identifiers inside an index expression
    // of a hierarchical reference (item 2).
    std::unordered_set<std::string_view> lp_names;
    for (const auto& [name, _] : cfg->local_params) lp_names.insert(name);

    // True iff `e`'s root walks down through nothing but identifier,
    // member-access, and select nodes — the form item 3 calls "the
    // hier identifier as the only term in the expression".  Indexes
    // inside a select are not part of the term tree; they are vetted
    // separately by item 2.
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

        // Item 3: a hierarchical identifier may not appear as a sub-
        // term of an arithmetic/logical expression (e.g. `top.W + 7`).
        if (has_hier && !is_pure_term_tree(expr)) {
          diag_.Error(
              cfg->range.start,
              std::format("config '{}' override of parameter '{}' embeds a "
                          "hierarchical identifier inside a larger "
                          "expression",
                          cfg->name, pname));
        }

        // Item 5: a select that feeds into a member-access on its
        // result is a mid-chain scope traversal (`top.arr[0].W`) and
        // is forbidden.  A select whose result is the whole expression
        // (`top.PARAM[2]`) is left to item 2.
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

        // Item 2: each identifier appearing inside a select index must
        // name a localparam declared in the same configuration; bare
        // literals carry no identifier and are accepted.
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

        // Item 6: only built-in (system) constant functions are
        // permitted; user-defined function calls are rejected.
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
    }
  }
}

void Elaborator::ValidatePackageExports() {
  // Build a map of package name to declaration for quick lookup.
  std::unordered_map<std::string_view, const PackageDecl*> pkg_by_name;
  for (const auto* pkg : unit_->packages) {
    pkg_by_name[pkg->name] = pkg;
  }

  // Decide whether `name` can be exported from `src_pkg` — either because
  // `src_pkg` declares it natively, or because `src_pkg` re-exports it
  // through its own export/import declarations. The recursion lets a name
  // travel down an arbitrarily long chain of re-exports; `visited` blocks
  // cycles through mutually-importing packages.
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
        // `export *::*;` — any of this package's imports may supply the name.
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
    // Gather what this package imports: direct "src::name" targets and the
    // set of source packages referenced by wildcard imports.
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
      // Forms `export *::*;` and `export p::*;` have no per-name validation;
      // they export whatever is actually imported.
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
      // A direct import of the same name, or any wildcard import from the
      // source package, satisfies the "actually imported" requirement; for
      // an unreferenced wildcard candidate the export itself counts as the
      // reference that completes the import.
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
    for (const auto* item : iface->items) {
      if (item->kind == ModuleItemKind::kClockingBlock &&
          !item->name.empty()) {
        clocking_names.insert(item->name);
      }
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
      // Identifiers declared locally in the module body but not as ports —
      // used to distinguish "declared but not a port" (reject) from
      // "never declared" (handled by name resolution elsewhere).
      std::unordered_set<std::string_view> local_signals;
      for (auto* mi : mod->items) {
        if ((mi->kind == ModuleItemKind::kNetDecl ||
             mi->kind == ModuleItemKind::kVarDecl) &&
            !mi->name.empty() && !port_map.contains(mi->name)) {
          local_signals.insert(mi->name);
        }
      }

      // §30.4.1: source shall be a net connected to an input or inout port.
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

      // §30.4.1: destination shall be a net or variable connected to an
      // output or inout port.
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

      // Timing-check terminals retain the prior ref-port rejection.
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

      // §30.4.4.4: Endpoints of an ifnone path must match its companion
      // if(cond) paths within the same specify block, and cannot coexist
      // with an unconditional path on the same endpoints.
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

      // §30.4.5: a parallel connection (=>) requires matching bit counts on
      // the source and destination. Full connections (*>) impose no such
      // constraint. If either side references a terminal whose width cannot
      // be determined at elaboration, skip the check rather than diagnose.
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

      // §30.7.4.1 / §30.7.4.2: pulse-filter style and showcancelled policy
      // are bound to an output at its first module-path mention. A later
      // pulsestyle or showcancelled/noshowcancelled declaration for the same
      // destination would contradict that binding, so we iterate items in
      // source order and flag any such redeclaration.
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

      // §30.5: delay values shall be constant expressions containing literals
      // or specparams. Any bare identifier must resolve to a specparam
      // declared in the same specify block.
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

// §3.1: Recursively collect all elaborated modules from the instantiation
// hierarchy into the design's all_modules map.
static void CollectAllModules(
    RtlirModule* mod,
    std::unordered_map<std::string_view, RtlirModule*>& all_modules) {
  if (!mod) return;
  auto [it, inserted] = all_modules.try_emplace(mod->name, mod);
  if (!inserted) return;  // Already visited (diamond instantiation).
  for (auto& child : mod->children) {
    CollectAllModules(child.resolved, all_modules);
  }
}

void Elaborator::RunPreElaborationValidations() {
  // §3.13: Validate definitions and package name spaces.
  ValidateNameSpaces();
  // §33.4.1.1: validate config design statements (cells must not name
  // configurations) and resolve omitted library identifiers.
  ValidateConfigDesignStatements();
  // §33.4.1.2: at most one default clause per config.
  ValidateConfigDefaultClauses();
  // §33.4.1.3: instance paths must start at a top-level design cell.
  ValidateConfigInstanceClauses();
  // §33.4.1.4: cell clauses with a library qualifier cannot use a
  // liblist expansion.
  ValidateConfigCellClauses();
  // §33.4.2: an instance clause may not name a path inside a
  // subhierarchy delegated to another config.
  ValidateConfigHierarchicalRules();
  // §33.4.3 item 1: localparams in a config must be literal-valued.
  ValidateConfigLocalparams();
  // §33.4.3 items 3, 5, 6: validate parameter override value expressions
  // attached to a use clause.
  ValidateConfigParamOverrides();
  // §24.6: Anonymous program items share the surrounding scope's name space.
  ValidateAnonymousProgramNameSharing();
  // §26.2: Reject package items that are nets with implicit continuous
  // assignments or processes (initial, final, always*).
  ValidatePackageItems();
  // §26.6: Validate package export declarations against the package's imports.
  ValidatePackageExports();
  // §25.5.4, §25.5.5: Validate modport port-id uniqueness, direction
  // legality, and clocking-block references.
  ValidateModports();
  // §30.4.1: Enforce module path source/destination port-direction and
  // net-kind restrictions.
  ValidateSpecifyBlocks();
  // §3.12.1: Register CU-scope typedefs and classes before module elaboration.
  RegisterCuScopeItems();
  // §8.13: Check that no class extends a :final class.
  ValidateFinalClassExtension();
  // §8.17: Validate chaining constructor rules.
  ValidateChainingConstructors();
  // §8.19: Validate constant class property rules.
  ValidateConstClassProperties();
  // §8.20: Validate virtual method override rules.
  ValidateVirtualMethodOverrides();
  // §8.21: Validate abstract class and pure virtual method rules.
  ValidateAbstractClassRules();
  // §8.24: Validate out-of-block method declarations.
  ValidateOutOfBlockDeclarations();
  // §8.26: Validate interface class rules.
  ValidateInterfaceClassRules();
  // §8.27: Validate forward class typedefs are resolved.
  ValidateForwardClassTypedefs();

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
    // §33.6.4: an instance-clause path is rooted at the design cell
    // name (e.g. `instance top.a2`), so seed the active path with the
    // top module's name before descending so children inherit the
    // correct prefix.
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
    // §23.11: Bind directives are applied after normal elaboration.
    ApplyBindDirectives(top);
    // §25.7.4: Detect duplicate modport exports across modules.
    ValidateModportExportConflicts(top);
    // §3.1: Register the full instantiation hierarchy in the design's
    // module map.
    CollectAllModules(top, design->all_modules);
  }

  // §3.12.1: CU-scope functions/tasks available to all modules.
  for (auto* item : unit_->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      design->cu_function_decls.push_back(item);
    } else if (item->kind == ModuleItemKind::kLetDecl) {
      design->cu_let_decls.push_back(item);
    }
  }
  // §20.6.2: Populate type widths for $bits(type) support.
  for (const auto& [name, dtype] : typedefs_) {
    design->type_widths[name] = EvalTypeWidth(dtype, typedefs_);
  }
  // §23.7: Pass package declarations for import resolution in the lowerer.
  design->packages = unit_->packages;
  // §23.7.1: Pass CU-scope class declarations for scope resolution.
  design->cu_class_decls.insert(design->cu_class_decls.end(),
                                unit_->classes.begin(), unit_->classes.end());
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
  RunPreElaborationValidations();

  // §33.6.2: a `default liblist` clause in the config replaces the
  // lib.map's declaration order with the listed libraries, and excludes
  // every other library from binding.  Apply the override before any
  // FindModule call so even the design-statement lookup sees it.
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

  // §33.6.3: a `cell <name> use <lib>.<cell>;` rule selects every
  // instance whose cell name is <name> and explicitly binds it to
  // <lib>.<cell>.  The binding is unconditional — it fires even when
  // the default liblist excludes <lib>, because §33.6.3 calls it an
  // "explicit" bind.  Record the mapping here so FindModule can apply
  // it transitively at every instance lookup, including the design
  // statement's own cells.
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kCell) continue;
    if (!rule->cell_lib.empty()) continue;
    if (rule->use_lib.empty() || rule->use_cell.empty()) continue;
    cell_clause_use_overrides_[std::string(rule->cell_name)] = {
        std::string(rule->use_lib), std::string(rule->use_cell)};
  }

  // §33.6.4: `instance <path> liblist <libs>;` overrides the binding
  // for the named instance and (because liblists are inherited) for
  // every descendant that no deeper rule reclaims.  Stash each rule
  // here keyed by its path; FindModule walks the list per lookup and
  // picks the most-specific matching prefix.
  for (auto* rule : cfg->rules) {
    if (rule->kind != ConfigRuleKind::kInstance) continue;
    if (rule->liblist.empty()) continue;
    std::vector<std::string> libs;
    libs.reserve(rule->liblist.size());
    for (auto lib : rule->liblist) libs.emplace_back(lib);
    instance_liblist_overrides_.emplace_back(std::string(rule->inst_path),
                                             std::move(libs));
  }

  // §33.6.5: an `instance <path> use <lib>.<cfg>:config;` rule
  // delegates the bindings of <path> and its descendants to a named
  // inner config.  The inner config's design statement supplies the
  // exact binding for the named instance; the inner config's other
  // rules supply bindings for descendants, with instance-clause
  // paths interpreted relative to the inner config's own top-level
  // module.  Translate each delegation into entries the existing
  // FindModule path-matching loops can resolve:
  //   - the inner design cell becomes a path-scoped use override for
  //     the outer instance itself (instance_use_overrides_)
  //   - the inner default liblist becomes an outer-instance liblist
  //     rule keyed at the delegated path
  //   - each inner instance liblist rule has its inner-relative path
  //     rewritten to start at the outer delegated path
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
    // Rewrite inner-relative paths to the outer namespace; the inner
    // top-level module name stands in for the delegated path's root.
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

  // §33.5.4: the cells named in the config's design statement are the
  // top-level modules.  Resolve each cell to its module declaration and
  // hand them all to the shared elaboration core.
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

// §3.12.1: Register CU-scope typedefs, classes, and imports so they are
// visible during module elaboration.
void Elaborator::RegisterCuScopeItems() {
  // §15.3: semaphore is a built-in class type in the std package.
  class_names_.insert("semaphore");
  // §15.4: mailbox is a built-in class type in the std package.
  class_names_.insert("mailbox");
  // §8.30.1: weak_reference is a built-in parameterized class in the std package.
  class_names_.insert("weak_reference");
  // §9.7: process is a built-in :final class.
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
  // §23.7.1: Register package parameters with qualified names for
  // scope-prefixed constant evaluation (e.g., pkg::WIDTH in dimensions).
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
      if (!mod->ports[i].name.empty() && !extern_decl->ports[i].name.empty() &&
          mod->ports[i].name != extern_decl->ports[i].name) {
        diag_.Error(mod->range.start,
                    std::format("module '{}' port '{}' at position {} does not "
                                "match extern declaration port '{}'",
                                mod->name, mod->ports[i].name, i,
                                extern_decl->ports[i].name));
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
    }
  }
}

ModuleDecl* Elaborator::FindModule(std::string_view name) const {
  // §33.6.5: when the current instance path exactly matches a path
  // delegated to an inner config, the inner config's design statement
  // dictates the binding for the named instance itself.  Resolve to
  // the recorded (lib, cell) directly and bypass library-order and
  // liblist filters; the binding is explicit per §33.6.5's "design
  // statement … defines the exact binding".
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

  // §33.6.3: "The cell clause selects all cells named m and explicitly
  // binds them to the gate representation in gateLib."  When a config's
  // cell clause names this lookup target, redirect to the named
  // (lib, cell) pair directly — bypassing both the library-order
  // priority of §33.6.1 and the strict-liblist exclusion of §33.6.2.
  if (auto it = cell_clause_use_overrides_.find(std::string(name));
      it != cell_clause_use_overrides_.end()) {
    const auto& target_lib = it->second.first;
    const auto& target_cell = it->second.second;
    for (auto* mod : unit_->modules) {
      if (mod->is_extern) continue;
      if (mod->library == target_lib && mod->name == target_cell) {
        return mod;
      }
    }
    return nullptr;
  }

  // §33.6.1: "all instances of module adder shall use aLib.adder
  // (because aLib is the first library specified that contains a cell
  // named adder)."  Collect every non-extern decl that matches `name`,
  // then break ties by library declaration order — if no order has been
  // registered, the first match wins, matching the prior behavior.
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

  // §33.6.4: pick the most-specific `instance ... liblist ...` rule
  // whose path equals current_inst_path_ or is a strict prefix of
  // it.  When such a rule matches, its liblist replaces the default
  // for this lookup — so libraries excluded by §33.6.2's default
  // become eligible again, and the inherited liblist follows the
  // hierarchy down through descendants.
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
    // §33.6.2: when a config's default liblist is active, drop any
    // candidate whose library is not on the liblist — those cells "shall
    // not be used" regardless of source order.
    if (library_order_strict_ && !candidates.empty()) {
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

  // §24: Programs can be instantiated like modules.
  auto pit = std::find_if(unit_->programs.begin(), unit_->programs.end(),
                          [name](auto* p) { return p->name == name; });
  if (pit != unit_->programs.end()) return *pit;

  // §25: Interfaces can be instantiated.
  auto iit = std::find_if(unit_->interfaces.begin(), unit_->interfaces.end(),
                          [name](auto* i) { return i->name == name; });
  if (iit != unit_->interfaces.end()) return *iit;

  // §17: Checkers can be instantiated.
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
  if (pd.has_decl_range || pd.has_decl_type) {
    pd.decl_width = EvalTypeWidth(dtype, typedefs, scope);
  }
}

int64_t ConvertOverrideValue(int64_t value, const RtlirParamDecl& pd) {
  if (!pd.has_decl_type && !pd.has_decl_range) return value;
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

RtlirModule* Elaborator::ElaborateModule(const ModuleDecl* decl,
                                         const ParamList& params) {
  auto* mod = arena_.Create<RtlirModule>();
  mod->name = decl->name;
  // §33.6.1: surface which library the bound cell came from so callers
  // can verify the default-binding choice.
  mod->library = decl->library;
  mod->has_param_port_list = decl->has_param_port_list;
  mod->is_program = (decl->decl_kind == ModuleDeclKind::kProgram);
  // §E.4-E.7: propagate delay mode directive.
  mod->delay_mode = unit_->delay_mode_directive;
  // §5.12: Resolve attributes on module definition.
  mod->attrs = ResolveAttributes(decl->attrs, diag_);

  // §26.7: every compilation unit wildcard-imports the built-in std package
  // implicitly, so the lowerer must see it among the module's imports.
  RtlirImport std_import;
  std_import.package_name = "std";
  std_import.is_wildcard = true;
  mod->imports.push_back(std_import);

  // §26.4: Header imports are visible throughout the module, including in
  // parameter and port declarations that follow.
  ApplyHeaderImports(decl);

  for (size_t i = 0; i < decl->params.size(); ++i) {
    const auto& [pname, pval] = decl->params[i];
    RtlirParamDecl pd;
    pd.name = pname;
    pd.default_value = pval;
    pd.is_resolved = false;
    pd.is_type_param = decl->type_param_names.count(pname) > 0;
    pd.is_localparam = decl->localparam_port_names.count(pname) > 0;

    // §23.10.3: build scope from already-resolved earlier parameters so that
    // range/type expressions and default values can reference them.
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
      } else {
        auto val = ConstEvalInt(pval, scope);
        pd.resolved_value = val.value_or(0);
        pd.is_resolved = val.has_value();
      }
    }

    mod->params.push_back(pd);
  }

  // §6.20.1: a value parameter with no default in the parameter port list
  // must be supplied at every instantiation of the design element. Type
  // parameters and localparam ports are validated elsewhere; the check here
  // catches a missing override on plain value parameters.
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
  // §27.6: assign external names to unnamed generate blocks before their
  // bodies are elaborated, so downstream uses of the name see a stable value.
  AssignGenerateBlockNames(decl);
  ElaborateItems(decl, mod);
  return mod;
}

// --- Port elaboration ---

void Elaborator::ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod) {
  auto param_scope = BuildParamScope(mod);
  // §23.2.2.1 R5: Duplicate explicit port name check for non-ANSI modules.
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
    // §6.14: chandle cannot be used as a port type.
    if (port.data_type.kind == DataTypeKind::kChandle) {
      diag_.Error(port.loc, "chandle cannot be used as a port type");
      continue;
    }
    if (port.data_type.kind == DataTypeKind::kVirtualInterface) {
      diag_.Error(port.loc,
                  "virtual interface cannot be used as a port type");
      continue;
    }

    // §23.2.2.1 R9: Non-ANSI implicit ports must have a direction declared
    // in the module body.
    if (decl->is_non_ansi_ports && !port.name.empty() &&
        !port.is_explicit_named && port.direction == Direction::kNone) {
      diag_.Error(port.loc,
                  std::format("port '{}' has no direction declaration in the "
                              "module body",
                              port.name));
    }

    // §23.2.2.1 R11/R12: Track complete vs partial port declarations for
    // body-level net/variable redeclaration validation.
    if (decl->is_non_ansi_ports && !port.name.empty() &&
        port.direction != Direction::kNone) {
      if (port.data_type.kind != DataTypeKind::kImplicit) {
        non_ansi_complete_ports_.insert(port.name);
      } else {
        non_ansi_partial_ports_[port.name] =
            EvalTypeWidth(port.data_type, typedefs_, param_scope);
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

// --- Module item elaboration ---

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

// §9.2.2.2: Check if a statement contains a fork-join construct.
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

// §9.2.2.2: Detect incomplete if/case that may infer latched behavior.
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

// §9.2.2.1: Check if a statement contains any timing control.
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
        InferSensitivity(proc.body, arena, nullptr, /*exclude_written=*/false);
  }
  // §9.2.2.1: Warn if a general-purpose always has no timing control.
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
  // §5.12: Resolve attributes.
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

// §9.2.2.2, §9.2.2.4: Check that always_comb/always_latch/always_ff LHS
// variables are not driven by other processes or continuous assignments.
void Elaborator::CheckAlwaysCombMultiDriver(const ModuleDecl* decl,
                                            RtlirModule* /*mod*/) {
  std::vector<ProcInfo> procs;
  std::unordered_set<std::string> cont_assign_lhs;
  CollectProcessLhsInfo(decl, procs, cont_assign_lhs, &func_decls_);
  CheckDriverConflicts(procs, cont_assign_lhs, diag_);
}

// §7.5: Check for dynamic array [] with init to infer size from elements.
static void InferDynArraySize(const std::vector<Expr*>& dims, const Expr* init,
                              RtlirVariable& var) {
  if (dims.empty() || dims[0] != nullptr) return;  // Not a dynamic array.
  if (var.is_queue || var.is_assoc) return;        // Already classified.
  var.is_dynamic = true;
  if (init && !init->elements.empty()) {
    var.unpacked_size = static_cast<uint32_t>(init->elements.size());
  }
}

// §7.4: Extract unpacked array size from dimension expressions.
// §7.10: Detect queue [$] or [$:N].
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

// §7.4: Parse range dimension [hi:lo] or [lo:hi].
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

// §7.8: Detect associative array index type [string], [int], [*], etc.
// §7.9.8: Map index type name to its bit-width for traversal validation.
static uint32_t AssocIndexWidth(std::string_view t) {
  if (t == "byte") return 8;
  if (t == "shortint") return 16;
  if (t == "longint") return 64;
  return 32;  // int, integer, *, default
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
    return true;
  }
  return false;
}

// §7.8.5: Check if an identifier is a user-defined type for assoc index.
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
  // §7.8.3/§7.8.5: User-defined type (class, struct, enum) as assoc index.
  if (dim->kind == ExprKind::kIdentifier &&
      IsUserDefinedType(dim->text, typedefs, class_names)) {
    var.is_assoc = true;
    // §7.8.3: Mark class-indexed associative arrays.
    if (class_names.count(dim->text) > 0) {
      var.is_class_index = true;
      var.assoc_index_class_name = dim->text;
      var.assoc_index_width = 64;  // Class handles are 64-bit.
    } else {
      // §7.8.5: Resolve typedef to compute index width.
      auto it = typedefs.find(dim->text);
      if (it != typedefs.end()) {
        var.assoc_index_width = EvalTypeWidth(it->second, typedefs);
      }
    }
    return;
  }
  if (TryParseRangeDim(dim, var)) return;
  // Simple size [N] — creates N elements indexed from 0.
  auto size_val = ConstEvalInt(dim);
  if (size_val && *size_val > 0) {
    var.unpacked_size = static_cast<uint32_t>(*size_val);
  }
}

void Elaborator::ElaborateNetDecl(ModuleItem* item, RtlirModule* mod) {
  if (ansi_port_names_.count(item->name)) {
    diag_.Error(item->loc,
                std::format("redeclaration of ANSI port '{}'", item->name));
  }
  // §23.2.2.1 R11: A complete port declaration cannot be redeclared.
  if (non_ansi_complete_ports_.count(item->name)) {
    diag_.Error(
        item->loc,
        std::format("redeclaration of port '{}' that has a complete port "
                    "declaration",
                    item->name));
  }
  // §23.2.2.1 R12: A partial port declaration allows a net/variable
  // redeclaration only if the vector ranges match.
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
  RtlirNet net;
  net.name = ScopedName(item->name);
  // §6.6.8: interconnect nets are typeless generic nets.
  if (item->data_type.is_interconnect) {
    net.net_type = NetType::kInterconnect;
    interconnect_names_.insert(item->name);
  } else {
    net.net_type = DataTypeToNetType(item->data_type.kind);
  }
  net.width = EvalTypeWidth(item->data_type, typedefs_);
  net.is_signed = IsSignedType(item->data_type, typedefs_);
  ValidatePackedDimRange(item->data_type, item->loc);
  // §6.7.1: Validate explicit net data type is 4-state.
  if (!item->data_type.is_interconnect) {
    DataTypeKind k = item->data_type.kind;
    if (k != DataTypeKind::kStruct && k != DataTypeKind::kUnion &&
        k != DataTypeKind::kEnum && k != DataTypeKind::kNamed &&
        DataTypeToNetType(k) == NetType::kWire &&
        k != DataTypeKind::kWire && !Is4stateType(k)) {
      diag_.Error(item->loc, "net data type must be 4-state");
    }
  }
  // §6.7 footnote 16: charge strength shall only be used with trireg.
  if (item->data_type.charge_strength != 0 &&
      net.net_type != NetType::kTrireg) {
    diag_.Error(item->loc,
                "charge strength can only be used with trireg nets");
  }
  net.is_vectored = item->data_type.is_vectored;
  net.is_scalared = item->data_type.is_scalared;
  // §6.7 footnote 16: vectored/scalared requires at least one packed dim.
  if ((item->data_type.is_vectored || item->data_type.is_scalared) &&
      net.width <= 1 && item->data_type.packed_dim_left == nullptr) {
    diag_.Error(item->loc,
                "vectored or scalared requires at least one packed dimension");
  }
  // §6.6.4: Extract charge strength and decay time for trireg nets.
  if (item->data_type.charge_strength != 0) {
    net.charge_strength =
        static_cast<Strength>(item->data_type.charge_strength);
  }
  // §E.3: apply `default_trireg_strength to trireg nets without explicit
  // strength.
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
    // §E.2: apply `default_decay_time to trireg nets without explicit decay.
    net.decay_ticks = unit_->default_decay_time;
  }
  // §5.12: Resolve attributes.
  net.attrs = ResolveAttributes(item->attrs, diag_);
  mod->nets.push_back(net);

  // §10.3.4: Drive strength on net decl applies only to scalar nets,
  // except supply0/supply1.
  if ((item->data_type.drive_strength0 != 0 ||
       item->data_type.drive_strength1 != 0) &&
      net.width > 1 && net.net_type != NetType::kSupply0 &&
      net.net_type != NetType::kSupply1) {
    diag_.Error(item->loc,
                "drive strength on continuous assignment applies only to "
                "scalar nets");
  }
  // §10.3.1: Net declaration assignment creates an implicit continuous assign.
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

// §6.23: Resolve type(expr) to concrete type kind from declared variables.
// §6.19/§6.24.2: Set enum type name on variable for $cast validation.
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
    // Arena-allocate copy: typedefs_ map is destroyed with the Elaborator,
    // but var.dtype must survive until after lowering.
    var.dtype = arena.Create<DataType>(it->second);
  }
}

// §7.2: Resolve struct/union type info for field-level access.
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
  // Arena-allocate copy: typedefs_ map is destroyed with the Elaborator,
  // but var.dtype must survive until after lowering.
  var.dtype = arena_.Create<DataType>(td->second);
}

void Elaborator::ValidateVarDeclTypes(ModuleItem* item) {
  // §8.4: Track class-typed variables for operator restriction checks.
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    class_var_names_.insert(item->name);
    class_var_types_[item->name] = item->data_type.type_name;
    // §8.25: Using the unadorned name of a parameterized class denotes the
    // default specialization. If any parameter lacks a default, the class has
    // no default specialization and the unadorned name is illegal.
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
    // §8.30.1: weak_reference parameter type T shall be a class type.
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
  ValidateAssocIndexType(item);
}

void Elaborator::TrackVarArrayInfo(const ModuleItem* item,
                                   const RtlirVariable& var) {
  if (item->unpacked_dims.empty()) return;
  VarArrayInfo info{item->data_type.kind,
                    var.unpacked_size,
                    static_cast<uint32_t>(item->unpacked_dims.size()),
                    var.width,
                    var.is_dynamic,
                    var.is_assoc,
                    {},
                    {}};
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

void Elaborator::ElaborateVarDecl(ModuleItem* item, RtlirModule* mod) {
  ResolveTypeRef(item, mod);
  // §6.25: Resolve parameterized class scope types (cls#(T)::member).
  ResolveParameterizedType(item->data_type);
  // §6.6.7: If the type is a user-defined nettype, create a net.
  if (item->data_type.kind == DataTypeKind::kNamed &&
      nettype_names_.count(item->data_type.type_name)) {
    item->data_type.is_net = true;
    item->kind = ModuleItemKind::kNetDecl;
    nettype_net_names_.insert(item->name);
    ElaborateNetDecl(item, mod);
    // §6.6.7: Tag the RtlirNet with user-nettype info.
    auto& net = mod->nets.back();
    net.is_user_nettype = true;
    net.nettype_name = item->data_type.type_name;
    auto it = nettype_resolve_funcs_.find(item->data_type.type_name);
    if (it != nettype_resolve_funcs_.end()) {
      net.resolve_func = it->second;
    }
    return;
  }
  // §6.8 footnote 14: automatic is illegal in a non-procedural data_declaration.
  if (item->is_automatic) {
    diag_.Error(item->loc,
                "automatic lifetime is not allowed on module-level variables");
  }
  if (ansi_port_names_.count(item->name)) {
    diag_.Error(item->loc,
                std::format("redeclaration of ANSI port '{}'", item->name));
  }
  // §23.2.2.1 R11: A complete port declaration cannot be redeclared.
  if (non_ansi_complete_ports_.count(item->name)) {
    diag_.Error(
        item->loc,
        std::format("redeclaration of port '{}' that has a complete port "
                    "declaration",
                    item->name));
  }
  // §23.2.2.1 R12: A partial port declaration allows a variable
  // redeclaration only if the vector ranges match.
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
  // §6.20.6: Const variables must have an initializer.
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
  if (item->data_type.kind == DataTypeKind::kNamed)
    var_named_types_[item->name] = item->data_type.type_name;
  if (item->data_type.kind == DataTypeKind::kVirtualInterface) {
    auto iface_name = item->data_type.type_name;
    auto modport_name = item->data_type.modport_name;
    vi_var_interface_types_[item->name] = iface_name;
    vi_var_modports_[item->name] = modport_name;
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
  var.elem_type_kind = item->data_type.kind;
  var.init_expr = item->init_expr;
  // §10.3.2: Track variables with initializers.
  if (item->init_expr) {
    var_init_names_.insert(item->name);
  }
  // Pass struct/union type info for field-level access.
  SetStructTypeInfo(item, var);
  // §8: Mark class-typed variables.
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    var.class_type_name = item->data_type.type_name;
  }
  // §6.19/§6.24.2: Track enum type for $cast validation.
  SetEnumTypeInfo(item, var, typedefs_, arena_);
  // §7.4/§7.5: Compute unpacked array element count.
  ComputeUnpackedDims(item->unpacked_dims, var, typedefs_, class_names_,
                      diag_, item->loc);
  ValidateUnpackedDimRange(item->unpacked_dims, item->loc);
  InferDynArraySize(item->unpacked_dims, item->init_expr, var);
  // §7.6/§7.9.9: Track array info for assignment compatibility.
  TrackVarArrayInfo(item, var);
  // §5.12: Resolve attributes.
  var.attrs = ResolveAttributes(item->attrs, diag_);
  mod->variables.push_back(var);
  ValidateArrayInitPattern(item);
  ValidateStructInitPattern(item);
  TrackEnumVariable(item);
  ValidateVarDeclTypes(item);
}

// --- §23.11: bind directives ---

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
  WalkForBind(top, std::string(top->name), binds, /*under_bind=*/false,
              visited);
}

void Elaborator::WalkForBind(RtlirModule* mod, const std::string& hier_path,
                             const std::vector<BindDirective*>& binds,
                             bool under_bind,
                             std::unordered_set<RtlirModule*>& visited) {
  if (!mod) return;
  if (!visited.insert(mod).second) return;

  // Determine which binds apply at this scope (hier_path / module name).
  for (auto* bd : binds) {
    bool applies = false;
    bool has_instances = !bd->target_instances.empty();
    bool is_scope = IsBindTargetScope(bd->target, unit_);
    if (is_scope && !has_instances) {
      // Form 1 designwide: apply to every instance of the named scope.
      if (mod->name == bd->target) applies = true;
    } else if (is_scope && has_instances) {
      // Form 1 with instance list: apply if hier_path matches an instance.
      if (mod->name == bd->target) {
        for (auto inst_path : bd->target_instances) {
          if (hier_path == inst_path) {
            applies = true;
            break;
          }
        }
      }
    } else {
      // Form 2: target is a hierarchical instance path; match exactly.
      if (hier_path == bd->target) applies = true;
    }
    if (!applies) continue;
    if (under_bind) {
      diag_.Error(bd->loc,
                  "bind target shall not be a scope created by a bind");
      continue;
    }
    ApplyBindInstance(bd, mod);
  }

  // Snapshot current children; binds applied during recursion are added to
  // deeper modules, not this one, so index-based iteration over the current
  // children is safe after all top-level binds at this scope are applied.
  size_t n = mod->children.size();
  for (size_t i = 0; i < n; ++i) {
    auto& c = mod->children[i];
    if (!c.resolved) continue;
    bool child_under_bind = under_bind || c.is_bound;
    std::string child_path = hier_path;
    child_path.push_back('.');
    child_path.append(c.inst_name.data(), c.inst_name.size());
    WalkForBind(c.resolved, child_path, binds, child_under_bind, visited);
  }
}

void Elaborator::ApplyBindInstance(BindDirective* bd, RtlirModule* target) {
  auto* item = bd->instantiation;
  if (!item) return;

  // §23.11 footnote 4: if the bind target scope is an interface, only
  // interface or checker instantiations are allowed.
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

  // Name clash check: the bound instance's name must not collide with any
  // existing name in the target scope, including previously-bound instances.
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

  // §23.11: actual signal references in the bound instantiation resolve in
  // the target scope.  Identifier connections must be visible there; $unit
  // scope declarations are not visible.
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

  // Elaborate the bound module fresh.
  ParamList empty_params;
  auto* resolved = ElaborateModule(child_decl, empty_params);
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;
  inst.resolved = resolved;
  inst.is_bound = true;

  // Populate port bindings mirroring BindPorts's basic behavior (name lookup).
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

}  // namespace

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

}  // namespace delta
