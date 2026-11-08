#include <algorithm>
#include <cstddef>
#include <format>
#include <functional>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_name_rules.h"
#include "elaborator/block_name_space.h"
#include "elaborator/class_method_reads.h"
#include "elaborator/covergroup_rules.h"
#include "elaborator/covergroup_variables.h"
#include "elaborator/data_declared_before_use.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_call_targets.h"
#include "elaborator/elaborator_enclosing_subroutines.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/scope_resolution_bases.h"
#include "elaborator/std_package.h"
#include "elaborator/string_numeric_assign.h"
#include "elaborator/type_eval.h"
#include "elaborator/unit_scope_order.h"
#include "elaborator/value_kind.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct BareCall {
  std::string_view name;
  SourceLoc loc;
  std::string_view delay_number;
};

struct ScopeWalk {
  std::unordered_set<std::string_view> local_names;
  std::vector<std::pair<std::string_view, SourceLoc>> proc_lhs;
  std::vector<BareCall> bare_calls;
  std::unordered_map<const Stmt*, std::string_view> delayed_bodies;
  std::vector<std::string_view> active_loop_vars;
};

size_t PushTypedForInitVars(const Stmt* s, ScopeWalk& out) {
  size_t pushed = 0;
  for (size_t k = 0; k < s->for_inits.size(); ++k) {
    if (k >= s->for_init_types.size()) break;
    if (s->for_init_types[k].kind == DataTypeKind::kImplicit) continue;
    const Stmt* init = s->for_inits[k];
    if (init && init->lhs && init->lhs->kind == ExprKind::kIdentifier) {
      out.active_loop_vars.push_back(init->lhs->text);
      ++pushed;
    }
  }
  return pushed;
}

size_t PushForeachVars(const Stmt* s, ScopeWalk& out) {
  size_t pushed = 0;
  for (auto v : s->foreach_vars) {
    if (v.empty()) continue;
    out.active_loop_vars.push_back(v);
    ++pushed;
  }
  return pushed;
}

const Expr* BareCallOf(const Stmt* s) {
  if (s == nullptr || s->kind != StmtKind::kExprStmt || s->expr == nullptr ||
      s->expr->kind != ExprKind::kIdentifier)
    return nullptr;
  return s->expr;
}

void CollectBareCall(const Stmt* s, ScopeWalk& out) {
  if (s->kind == StmtKind::kDelay && s->delay != nullptr &&
      (s->delay->kind == ExprKind::kIntegerLiteral ||
       s->delay->kind == ExprKind::kRealLiteral) &&
      BareCallOf(s->body) != nullptr) {
    out.delayed_bodies[s->body] = s->delay->text;
  }
  const Expr* call = BareCallOf(s);
  if (call == nullptr) return;
  auto it = out.delayed_bodies.find(s);
  std::string_view delay_number =
      it == out.delayed_bodies.end() ? std::string_view{} : it->second;
  out.bare_calls.push_back({call->text, call->range.start, delay_number});
}

void CollectScopeWalk(const Stmt* s, ScopeWalk& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    out.local_names.insert(s->var_name);
  }
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->lhs->kind == ExprKind::kIdentifier &&
      std::find(out.active_loop_vars.begin(), out.active_loop_vars.end(),
                s->lhs->text) == out.active_loop_vars.end()) {
    out.proc_lhs.emplace_back(s->lhs->text, s->range.start);
  }
  CollectBareCall(s, out);
  size_t pushed = PushTypedForInitVars(s, out) + PushForeachVars(s, out);
  ForEachChildStmtWithBindings(
      s,
      [&](const Stmt* sub, const std::unordered_set<std::string_view>& bound) {
        out.active_loop_vars.insert(out.active_loop_vars.end(), bound.begin(),
                                    bound.end());
        CollectScopeWalk(sub, out);
        out.active_loop_vars.resize(out.active_loop_vars.size() - bound.size());
      });
  out.active_loop_vars.resize(out.active_loop_vars.size() - pushed);
}

void ValidateLocalWeakRefDecls(
    const Stmt* s, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl &&
      s->var_decl_type.type_name == "weak_reference" &&
      !s->var_decl_type.type_params.empty()) {
    const auto& tp = s->var_decl_type.type_params[0];
    if (!WeakRefTypeParamNamesClass(tp, typedefs, class_names)) {
      diag.Error(s->range.start,
                 "weak_reference needs a class type as its type parameter",
                 Subclause("8.30.1"));
    }
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    ValidateLocalWeakRefDecls(sub, typedefs, class_names, diag);
  });
}

}  // namespace

bool PackageDeclared(const CompilationUnit* unit, std::string_view pkg_name) {
  if (pkg_name == "std") return true;
  for (const auto* pkg : unit->packages) {
    if (pkg->name == pkg_name) return true;
  }
  return false;
}

std::string_view ProvidedNameOrigin(const CompilationUnit* unit,
                                    ProvidedNameCache& provided_cache,
                                    std::string_view pkg_name,
                                    std::string_view name) {
  auto it = provided_cache.find(pkg_name);
  if (it == provided_cache.end()) {
    PopulatePackageProvidedNames(unit, pkg_name, provided_cache[pkg_name]);
    it = provided_cache.find(pkg_name);
  }
  auto found = it->second.find(name);
  return found == it->second.end() ? std::string_view() : found->second;
}

bool PackageProvidesName(const CompilationUnit* unit,
                         ProvidedNameCache& provided_cache,
                         std::string_view pkg_name, std::string_view name) {
  return !ProvidedNameOrigin(unit, provided_cache, pkg_name, name).empty();
}

bool ImportsProvideName(const CompilationUnit* unit,
                        ProvidedNameCache& provided_cache,
                        const std::vector<ModuleItem*>& items,
                        std::string_view name) {
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& imp = item->import_item;
    bool provided =
        imp.is_wildcard
            ? PackageProvidesName(unit, provided_cache, imp.package_name, name)
            : imp.item_name == name;
    if (provided) return true;
  }
  return false;
}

static bool UnitDeclaresSubroutine(const CompilationUnit* unit,
                                   std::string_view name) {
  for (const auto* item : unit->cu_items) {
    if ((item->kind == ModuleItemKind::kTaskDecl ||
         item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kDpiImport) &&
        item->name == name) {
      return true;
    }
  }
  return false;
}

static bool IsTimeUnitName(std::string_view name) {
  return name == "s" || name == "ms" || name == "us" || name == "ns" ||
         name == "ps" || name == "fs";
}

static void ReportBareCallsNamingNothing(
    const ScopeWalk& walk, const std::function<bool(std::string_view)>& visible,
    DiagEngine& diag) {
  for (const auto& call : walk.bare_calls) {
    if (visible(call.name)) continue;
    if (!call.delay_number.empty() && IsTimeUnitName(call.name)) {
      diag.Error(call.loc,
                 std::format("'{}' after the delay {} is a separate token "
                             "that names no task; a time literal's unit "
                             "follows its number without white space",
                             call.name, call.delay_number),
                 Subclause("5.8"));
      continue;
    }
    diag.Error(call.loc, std::format("undeclared identifier '{}'", call.name),
               Subclause("23.9"));
  }
}

void Elaborator::ValidateScopeRules(const ModuleDecl* decl) {
  ScopeWalk walk;
  std::vector<BlockLabel> labels;
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      CollectScopeWalk(item->body, walk);
      CollectNameSpaceLabels(item->body, labels);
      ValidateLocalWeakRefDecls(item->body, typedefs_, class_names_, diag_);
      CheckNestedBlockNameSpaces(item->body, diag_);
    }
  }
  CollectAssertionNameSpaceLabels(decl->items, labels);
  for (const auto& [label, loc] : labels) DeclareInModuleNameSpace(label, loc);
  const std::vector<ModuleItem*> kUnitBefore =
      UnitItemsBefore(unit_, decl->range.start);
  const EnclosingImports kEnclosingImports = EnclosingImportsOf(*unit_, *decl);
  auto target_visible = [&](std::string_view name) {
    return walk.local_names.count(name) != 0 || IsNameInModuleScope(name) ||
           ImportsProvideName(unit_, pkg_provided_names_, decl->items, name) ||
           ImportsProvideName(unit_, pkg_provided_names_,
                              kEnclosingImports.above, name) ||
           ImportsProvideName(unit_, pkg_provided_names_, kUnitBefore, name) ||
           UnitDeclaresData(unit_, name, decl->range.start);
  };
  for (const auto& [name, loc] : walk.proc_lhs) {
    if (target_visible(name)) continue;
    diag_.Error(loc, std::format("undeclared identifier '{}'", name),
                Subclause("23.9"));
  }
  const std::unordered_set<std::string_view> kAbove =
      EnclosingSubroutineNames(*unit_, decl->name);
  const std::function<bool(std::string_view)> kCallVisible =
      [&](std::string_view name) {
        return target_visible(name) ||
               ImportsProvideName(unit_, pkg_provided_names_,
                                  kEnclosingImports.explicit_below, name) ||
               UnitDeclaresSubroutine(unit_, name) || kAbove.contains(name);
      };
  ReportBareCallsNamingNothing(walk, kCallVisible, diag_);
  ReportCallsOfDataNames(*decl, *unit_, kCallVisible, diag_);
}

namespace {

std::unordered_set<std::string_view> DeclaredGenvars(
    const std::vector<ModuleItem*>& items) {
  std::unordered_set<std::string_view> genvars;
  for (const auto* item : items) {
    if (item->is_genvar && !item->name.empty()) genvars.insert(item->name);
  }
  return genvars;
}

bool NamesScopeRandomize(std::string_view name) { return name == "randomize"; }

template <typename Pred>
void ReportUnresolvedRefs(const std::vector<const Expr*>& refs, Pred declared,
                          DiagEngine& diag,
                          const std::unordered_set<std::string_view>& genvars) {
  for (const auto* e : refs) {
    if (genvars.contains(e->text)) {
      diag.Error(e->range.start,
                 std::format("genvar '{}' is referenced outside a loop "
                             "generate scheme",
                             e->text),
                 Subclause("27.4"));
      continue;
    }
    if (declared(e->text) || NamesScopeRandomize(e->text)) continue;
    diag.Error(e->range.start,
               std::format("reference to unresolved identifier '{}'", e->text),
               Subclause("23.9"));
  }
}

template <typename Pred>
void ReportProcUnresolved(const ModuleDecl* decl, Pred declared,
                          DiagEngine& diag) {
  std::unordered_set<std::string_view> locals;
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      CollectProcReadableNames(item->body, locals);
  }
  std::vector<const Expr*> refs;
  for (const auto* item : decl->items) {
    if (!IsProceduralItemKind(item->kind)) continue;
    CollectProcRhsIdents(item->body, locals, refs);
    for (const EventExpr& ev : item->sensitivity) {
      CollectBareIdents(ev.signal, refs);
      CollectBareIdents(ev.iff_condition, refs);
    }
  }
  ReportUnresolvedRefs(refs, declared, diag, DeclaredGenvars(decl->items));
}

template <typename Pred>
void ReportDeclReadsUnresolved(const ModuleDecl* decl, Pred declared,
                               DiagEngine& diag) {
  std::vector<const Expr*> refs;
  for (const auto* item : decl->items) {
    bool is_data_decl = item->kind == ModuleItemKind::kVarDecl ||
                        item->kind == ModuleItemKind::kNetDecl;
    if (!is_data_decl) continue;
    CollectBareIdents(item->init_expr, refs);
    CollectBareIdents(item->data_type.type_ref_expr, refs);
  }
  ReportUnresolvedRefs(refs, declared, diag, DeclaredGenvars(decl->items));
}

void CollectItemConstantPositions(const ModuleItem* item,
                                  std::vector<const Expr*>& out) {
  if (item->kind == ModuleItemKind::kParamDecl)
    CollectBareIdents(item->init_expr, out);
  for (const Expr* e :
       {item->gen_cond, item->data_type.packed_dim_left,
        item->data_type.packed_dim_right, item->assign_delay,
        item->assign_delay_fall, item->assign_delay_decay, item->net_delay,
        item->net_delay_fall, item->net_delay_decay})
    CollectBareIdents(e, out);
  for (const auto& [left, right] : item->data_type.extra_packed_dims) {
    CollectBareIdents(left, out);
    CollectBareIdents(right, out);
  }
  for (const Expr* dim : item->unpacked_dims) CollectBareIdents(dim, out);
}

void CollectGenvarConstantPositions(const std::vector<ModuleItem*>& items,
                                    std::vector<const Expr*>& out) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kGenerateFor) continue;
    CollectItemConstantPositions(item, out);
    CollectGenvarConstantPositions(item->gen_body, out);
    if (item->gen_else != nullptr)
      CollectGenvarConstantPositions({item->gen_else}, out);
    for (const auto& case_item : item->gen_case_items) {
      for (const Expr* pattern : case_item.patterns)
        CollectBareIdents(pattern, out);
      CollectGenvarConstantPositions(case_item.body, out);
    }
  }
}

void ReportGenvarConstantMisuse(const ModuleDecl* decl, DiagEngine& diag) {
  std::vector<const Expr*> refs;
  CollectGenvarConstantPositions(decl->items, refs);
  ReportUnresolvedRefs(
      refs, [](std::string_view) { return true; }, diag,
      DeclaredGenvars(decl->items));
}

std::vector<ModuleItem*> SubroutineBodyImports(const ModuleItem* item) {
  std::vector<ModuleItem*> imports;
  for (const auto* stmt : item->func_body_stmts) {
    if (stmt == nullptr || stmt->kind != StmtKind::kBlockItemDecl) continue;
    if (stmt->decl_item == nullptr ||
        stmt->decl_item->kind != ModuleItemKind::kImportDecl) {
      continue;
    }
    imports.push_back(stmt->decl_item);
  }
  return imports;
}

template <typename Pred>
void ReportSubroutineUnresolved(const std::vector<ModuleItem*>& items,
                                Pred declared, const CompilationUnit* unit,
                                ProvidedNameCache& provided_cache,
                                DiagEngine& diag) {
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kTaskDecl &&
        item->kind != ModuleItemKind::kFunctionDecl) {
      continue;
    }
    if (!item->method_class.empty()) continue;
    std::unordered_set<std::string_view> locals;
    CollectSubroutineLocalNames(item, locals);
    std::vector<const Expr*> refs;
    for (const auto* stmt : item->func_body_stmts) {
      CollectProcRhsIdents(stmt, locals, refs);
    }
    std::vector<ModuleItem*> body_imports = SubroutineBodyImports(item);
    auto declared_in_body = [&](std::string_view n) {
      return declared(n) ||
             ImportsProvideName(unit, provided_cache, body_imports, n);
    };
    ReportUnresolvedRefs(refs, declared_in_body, diag, DeclaredGenvars(items));
  }
}

template <typename Provided>
void ReportUnprovidedPackageMember(const Expr* ref, Provided provided,
                                   DiagEngine& diag) {
  const Expr* member = ref->rhs;
  if (member == nullptr || member->kind != ExprKind::kIdentifier) return;
  if (provided(ref->lhs->text, member->text)) return;
  diag.Error(ref->lhs->range.start,
             std::format("reference to '{}::{}', which package '{}' neither "
                         "declares nor exports",
                         ref->lhs->text, member->text, ref->lhs->text),
             Subclause("26.3"));
}

template <typename Pred, typename Provided>
void ReportUnknownScopeBases(const ModuleDecl* decl, Pred known,
                             Provided provided, DiagEngine& diag) {
  std::vector<const Expr*> refs;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CollectScopeBases(item->assign_rhs, refs);
    } else if (IsProceduralItemKind(item->kind)) {
      CollectProcScopeBases(item->body, refs);
    }
  }
  for (const auto* ref : refs) {
    const Expr* b = ref->lhs;
    if (b->text == "local") continue;
    if (b->text == "std") {
      ReportUnprovidedPackageMember(
          ref,
          [](std::string_view, std::string_view member) {
            return StdPackageMemberNamed(member).has_value();
          },
          diag);
      continue;
    }
    if (known(b->text)) {
      ReportUnprovidedPackageMember(ref, provided, diag);
      continue;
    }
    diag.Error(
        b->range.start,
        std::format("reference to unresolved package or scope '{}'", b->text),
        Subclause("26.3"));
  }
}

bool IsKnownScopeBase(std::string_view n,
                      const std::unordered_set<std::string_view>& cu_scope,
                      const std::unordered_set<std::string_view>& classes,
                      const TypedefMap& typedefs, const CompilationUnit* unit) {
  if (cu_scope.count(n) != 0 || classes.count(n) != 0 ||
      typedefs.count(n) != 0) {
    return true;
  }
  for (const auto* pkg : unit->packages) {
    if (pkg->name == n) return true;
  }
  return false;
}

}  // namespace

bool Elaborator::IsDeclaredNameForRhs(std::string_view name) const {
  return var_types_.count(name) != 0 || sequence_names_.count(name) != 0 ||
         IsNameInModuleScope(name) || typedefs_.count(name) != 0 ||
         nettype_names_.count(name) != 0 ||
         assoc_typedef_names_.count(name) != 0 ||
         cu_scope_names_.count(name) != 0;
}

static std::unordered_set<std::string_view> ExplicitlyImportedNames(
    const RtlirModule* mod) {
  std::unordered_set<std::string_view> explicit_imported;
  for (const auto& imp : mod->imports) {
    if (!imp.is_wildcard && !imp.item_name.empty()) {
      explicit_imported.insert(imp.item_name);
    }
  }
  return explicit_imported;
}

static bool AnyPackageProvidesName(const CompilationUnit* unit,
                                   ProvidedNameCache& provided_cache,
                                   const std::vector<std::string_view>& pkgs,
                                   std::string_view name) {
  for (auto pkg : pkgs) {
    if (PackageProvidesName(unit, provided_cache, pkg, name)) return true;
  }
  return false;
}

template <typename Declared>
static void ReportContAssignUnresolved(const ModuleDecl* decl,
                                       const Declared& declared,
                                       DiagEngine& diag) {
  std::vector<const Expr*> refs;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    CollectBareIdents(item->assign_rhs, refs);
  }
  ReportUnresolvedRefs(refs, declared, diag, DeclaredGenvars(decl->items));
}

static std::unordered_set<std::string_view> UnpackedArrayNames(
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        infos) {
  std::unordered_set<std::string_view> names;
  for (const auto& entry : infos) names.insert(entry.first);
  return names;
}

void Elaborator::ValidateUnresolvedReferences(const ModuleDecl* decl,
                                              const RtlirModule* mod) {
  if (!mod) return;

  CheckStringNumericAssignments(decl->items, var_types_,
                                UnpackedArrayNames(var_array_info_), diag_);

  std::unordered_set<std::string_view> explicit_imported =
      ExplicitlyImportedNames(mod);
  std::vector<std::string_view> wildcard_packages =
      WildcardImportedPackages(mod);
  std::unordered_set<std::string_view> generate_names;
  CollectModuleGenerateNames(decl->items, generate_names);
  auto declared = [this, decl, &explicit_imported, &wildcard_packages,
                   &generate_names](std::string_view n) {
    bool unit_later =
        (UnitDataDeclaredOnlyAfter(unit_, n, decl->range.start) &&
         var_types_.count(n) == 0 && !IsNameInModuleScope(n)) ||
        (UnitConstantDeclaredOnlyAfter(unit_, n, decl->range.start) &&
         !ModuleDeclaresName(decl, n) && !IsNameInEnclosingScope(n));
    return (!unit_later && IsDeclaredNameForRhs(n)) ||
           explicit_imported.count(n) != 0 || generate_names.count(n) != 0 ||
           AnyPackageProvidesName(unit_, pkg_provided_names_, wildcard_packages,
                                  n);
  };
  ReportUnitScopedReferences(decl->items, unit_, diag_);
  ReportDataUsedAboveItsDeclaration(
      *decl, *mod, *unit_,
      [this](std::string_view n) { return IsNameInEnclosingScope(n); }, diag_);

  const ValueScope kValues{var_types_,  var_named_types_, var_array_info_,
                           func_decls_, typedefs_,        class_names_};
  ValidateModuleCovergroups(decl, {kValues, const_names_}, declared, diag_);
  ValidateCovergroupTypeCalls(
      decl,
      [this, mod](std::string_view n) {
        return VisibleCovergroup(n, mod, unit_) != nullptr;
      },
      diag_);
  ReportContAssignUnresolved(decl, declared, diag_);
  ReportProcUnresolved(decl, declared, diag_);
  ReportDeclReadsUnresolved(decl, declared, diag_);
  ReportGenvarConstantMisuse(decl, diag_);
  ReportAssertionUnresolved(decl, declared, diag_);
  ReportNonConstantBoundActuals(
      decl,
      [this](std::string_view n) {
        return var_types_.count(n) != 0 && const_names_.count(n) == 0;
      },
      diag_);
  ReportSubroutineUnresolved(decl->items, declared, unit_, pkg_provided_names_,
                             diag_);
  if (!unit_hier_head_names_) {
    AssignUnitGenerateBlockNames(unit_, arena_);
    unit_hier_head_names_ = std::make_shared<const UnitHierHeadNames>(unit_);
  }
  std::unordered_set<std::string_view> own_unnamed_blocks =
      UnnamedGenerateBlockNames(decl);
  ReportUnresolvedHierHeads(
      decl,
      [this, &declared, &own_unnamed_blocks](std::string_view n) {
        return declared(n) || own_unnamed_blocks.contains(n) ||
               unit_hier_head_names_->Admits(n);
      },
      diag_);
  ReportUndeclaredGenerateBlockMembers(decl, diag_);
  ReportUnnamedGenerateBlockReaches(decl, diag_);

  auto provided = [this](std::string_view base, std::string_view member) {
    bool unit_package = base != "std" && PackageDeclared(unit_, base) &&
                        class_names_.count(base) == 0 &&
                        typedefs_.count(base) == 0;
    if (!unit_package) return true;
    if (PackageProvidesName(unit_, pkg_provided_names_, base, member)) {
      return true;
    }
    std::string key = std::string(base) + "." + std::string(member);
    return cu_param_scope_.count(key) != 0;
  };
  ReportUnknownScopeBases(
      decl,
      [this, mod, &explicit_imported, &wildcard_packages](std::string_view n) {
        return IsKnownScopeBase(n, cu_scope_names_, class_names_, typedefs_,
                                unit_) ||
               VisibleCovergroup(n, mod, unit_) != nullptr ||
               explicit_imported.count(n) != 0 ||
               AnyPackageProvidesName(unit_, pkg_provided_names_,
                                      wildcard_packages, n);
      },
      provided, diag_);
}

static std::unordered_set<std::string> PackageDeclaredNames(
    const PackageDecl* pkg, const ScopeMap& constants) {
  std::unordered_set<std::string> pkg_names;
  for (const auto* item : pkg->items) {
    if (item == nullptr) continue;
    if (!item->name.empty()) pkg_names.insert(std::string(item->name));
    ForEachEnumTypeOfItem(
        item, [&](std::string_view, const DataType& enum_type) {
          for (const auto& member : enum_type.enum_members) {
            for (auto& n : EnumMemberDeclaredNames(member, constants))
              pkg_names.insert(std::move(n));
          }
        });
  }
  return pkg_names;
}

static bool UnitDeclaresWith(const CompilationUnit* unit,
                             const UnitScopeNames& names,
                             ProvidedNameCache& provided_cache,
                             const std::vector<ModuleItem*>& imports,
                             std::string_view n) {
  return names.item_names.count(n) != 0 || names.constants.count(n) != 0 ||
         names.typedefs.count(n) != 0 || names.class_names.count(n) != 0 ||
         ImportsProvideName(unit, provided_cache, imports, n);
}

void ReportUnresolvedInUnitSubroutines(const CompilationUnit* unit,
                                       const UnitScopeNames& names,
                                       ProvidedNameCache& provided_cache,
                                       DiagEngine& diag) {
  for (auto* sub : unit->cu_items) {
    const std::vector<ModuleItem*> kBefore = UnitItemsBefore(unit, sub->loc);
    auto declared_before = [&](std::string_view n) {
      return UnitDataDeclaredOnlyAfter(unit, n, sub->loc)
                 ? ImportsProvideName(unit, provided_cache, kBefore, n)
                 : UnitDeclaresWith(unit, names, provided_cache, kBefore, n);
    };
    ReportSubroutineUnresolved(std::vector<ModuleItem*>{sub}, declared_before,
                               unit, provided_cache, diag);
  }
  ReportUnitScopedReferences(unit->cu_items, unit, diag);
}

void ReportUnresolvedInPackageSubroutines(const CompilationUnit* unit,
                                          const UnitScopeNames& names,
                                          ProvidedNameCache& provided_cache,
                                          DiagEngine& diag) {
  for (const auto* pkg : unit->packages) {
    if (pkg == nullptr) continue;
    std::unordered_set<std::string> pkg_names =
        PackageDeclaredNames(pkg, names.constants);
    auto pkg_declares = [&](std::string_view n) {
      return pkg_names.count(std::string(n)) != 0 ||
             UnitDeclaresWith(unit, names, provided_cache, unit->cu_items, n) ||
             ImportsProvideName(unit, provided_cache, pkg->items, n);
    };
    ReportSubroutineUnresolved(pkg->items, pkg_declares, unit, provided_cache,
                               diag);
  }
}

}  // namespace delta
