#include <algorithm>
#include <format>
#include <functional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/std_package.h"
#include "elaborator/unit_scope_order.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

void WalkExprIdents(Expr* e, std::vector<Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    WalkExprIdents(e->lhs, out);
    return;
  }
  WalkExprIdents(e->lhs, out);
  WalkExprIdents(e->rhs, out);
  WalkExprIdents(e->base, out);
  WalkExprIdents(e->index, out);
  WalkExprIdents(e->index_end, out);
  WalkExprIdents(e->condition, out);
  WalkExprIdents(e->true_expr, out);
  WalkExprIdents(e->false_expr, out);
  WalkExprIdents(e->repeat_count, out);
  WalkExprIdents(e->with_expr, out);
  WalkExprIdents(e->stream_range, out);
  for (auto* a : e->args) WalkExprIdents(a, out);
  for (auto* el : e->elements) WalkExprIdents(el, out);
}

void WalkStmtScalarIdents(const Stmt* s, std::vector<Expr*>& out) {
  WalkExprIdents(s->condition, out);
  WalkExprIdents(s->lhs, out);
  WalkExprIdents(s->rhs, out);
  WalkExprIdents(s->delay, out);
  WalkExprIdents(s->cycle_delay, out);
  WalkExprIdents(s->for_cond, out);
  WalkExprIdents(s->expr, out);
  WalkExprIdents(s->assert_expr, out);
  WalkExprIdents(s->repeat_event_count, out);
  WalkExprIdents(s->var_init, out);
  for (auto* e : s->wait_order_events) WalkExprIdents(e, out);
}

void WalkStmtCaseIdents(const Stmt* s, std::vector<Expr*>& out) {
  for (const auto& ci : s->case_items) {
    for (auto* p : ci.patterns) WalkExprIdents(p, out);
  }
  for (const auto& rc : s->randcase_items) WalkExprIdents(rc.first, out);
}

void WalkStmtIdents(const Stmt* s, std::vector<Expr*>& out) {
  if (!s) return;
  WalkStmtScalarIdents(s, out);
  WalkStmtCaseIdents(s, out);
  ForEachChildStmt(s, [&](Stmt* const& sub) { WalkStmtIdents(sub, out); });
}

using OuterBoundRefs =
    std::unordered_map<std::string_view,
                       std::vector<std::pair<Expr*, std::string_view>>>;

struct LateImportCheck {
  const std::vector<std::string_view>& wildcards;
  std::function<bool(std::string_view)> module_declares;
  std::function<bool(std::string_view)> unit_data;
  std::function<bool(std::string_view)> declared;
};

struct ImportRuleCtx {
  DiagEngine& diag;
  const CompilationUnit* unit;
  ProvidedNameCache& pkg_provided_names;
  std::unordered_map<std::string_view, std::pair<std::string_view, SourceLoc>>&
      explicit_imports;
  std::vector<std::string_view>& wildcard_packages;
  std::unordered_map<std::string_view, SourceLoc>& wildcard_claimed;
  std::unordered_set<std::string_view>& seen_decls;
  OuterBoundRefs& outer_bound;
  ImportRuleCtx* outer;
  const LateImportCheck* late = nullptr;
};

void TrackImportRuleDecl(ImportRuleCtx& ctx, std::string_view name,
                         SourceLoc loc) {
  if (name.empty()) return;
  auto wit = ctx.wildcard_claimed.find(name);
  if (wit != ctx.wildcard_claimed.end()) {
    ctx.diag.Error(loc,
                   std::format("declaration of '{}' follows a reference "
                               "resolved through a wildcard package import",
                               name),
                   Subclause("26.3"));
  }
  ctx.seen_decls.insert(name);
  auto bound = ctx.outer_bound.find(name);
  if (bound == ctx.outer_bound.end()) return;
  for (auto& [ref, origin] : bound->second) ref->scope_prefix = origin;
  ctx.outer_bound.erase(bound);
}

bool ClaimWildcardCandidate(ImportRuleCtx& ctx, const Expr* e) {
  auto name = e->text;
  std::vector<std::string_view> providers;
  std::unordered_set<std::string_view> origins;
  for (auto pkg : ctx.wildcard_packages) {
    std::string_view origin =
        ProvidedNameOrigin(ctx.unit, ctx.pkg_provided_names, pkg, name);
    if (origin.empty()) continue;
    if (origins.insert(origin).second) providers.push_back(pkg);
  }
  if (providers.size() > 1) {
    ctx.diag.Error(
        e->range.start,
        std::format("reference to '{}' is ambiguous between wildcard "
                    "imports of packages '{}' and '{}'",
                    name, providers[0], providers[1]),
        Subclause("26.3"));
    return true;
  }
  if (providers.empty()) return false;
  ctx.wildcard_claimed[name] = e->range.start;
  ctx.seen_decls.insert(name);
  return true;
}

std::string_view ExplicitImportOrigin(ImportRuleCtx& ctx,
                                      std::string_view pkg_name,
                                      std::string_view name) {
  std::string_view origin =
      ProvidedNameOrigin(ctx.unit, ctx.pkg_provided_names, pkg_name, name);
  return origin.empty() ? pkg_name : origin;
}

std::string_view WildcardClaimOrigin(ImportRuleCtx& ctx,
                                     std::string_view name) {
  for (auto pkg : ctx.wildcard_packages) {
    std::string_view origin =
        ProvidedNameOrigin(ctx.unit, ctx.pkg_provided_names, pkg, name);
    if (!origin.empty()) return origin;
  }
  return {};
}

std::string_view WildcardOriginAmong(
    ImportRuleCtx& ctx, const std::vector<std::string_view>& packages,
    std::string_view name) {
  for (auto pkg : packages) {
    if (PackageProvidesName(ctx.unit, ctx.pkg_provided_names, pkg, name)) {
      return pkg;
    }
  }
  return {};
}

void NoteOuterBinding(ImportRuleCtx& from, ImportRuleCtx& binder, Expr* e) {
  std::string_view origin = WildcardClaimOrigin(binder, e->text);
  for (ImportRuleCtx* scope = &from; scope != &binder; scope = scope->outer) {
    scope->outer_bound[e->text].push_back({e, origin});
  }
}

void SettleReferenceBeforeImport(ImportRuleCtx& module, Expr* e) {
  const LateImportCheck& late = *module.late;
  std::string_view name = e->text;
  std::string_view later = WildcardOriginAmong(module, late.wildcards, name);
  if (later.empty() || late.module_declares(name)) return;
  if (late.unit_data(name)) {
    e->scope_prefix = "$unit";
    return;
  }
  if (late.declared(name)) return;
  module.diag.Error(e->range.start,
                    std::format("reference to '{}' precedes the wildcard "
                                "import of package '{}' that declares it",
                                name, later),
                    Subclause("26.3"));
}

void ProcessImportRuleRef(ImportRuleCtx& ctx, Expr* e) {
  auto name = e->text;
  if (name.empty()) return;
  ImportRuleCtx* module = &ctx;
  for (ImportRuleCtx* scope = &ctx; scope != nullptr; scope = scope->outer) {
    module = scope;
    if (scope->seen_decls.count(name)) {
      if (scope->wildcard_claimed.count(name)) NoteOuterBinding(ctx, *scope, e);
      return;
    }
    if (ClaimWildcardCandidate(*scope, e)) {
      NoteOuterBinding(ctx, *scope, e);
      return;
    }
  }
  SettleReferenceBeforeImport(*module, e);
}

bool CheckAgainstEarlierExplicitImport(ImportRuleCtx& ctx,
                                       const ModuleItem* item,
                                       std::string_view pkg_name) {
  auto name = item->import_item.item_name;
  auto eit = ctx.explicit_imports.find(name);
  if (eit == ctx.explicit_imports.end()) return false;
  std::string_view earlier = eit->second.first;
  if (ExplicitImportOrigin(ctx, earlier, name) ==
      ExplicitImportOrigin(ctx, pkg_name, name)) {
    return true;
  }
  ctx.diag.Error(item->loc,
                 std::format("explicit import of '{}::{}' conflicts with "
                             "earlier explicit import from '{}'",
                             pkg_name, name, earlier),
                 Subclause("26.3"));
  return true;
}

bool ReportExplicitImportAfterWildcardClaim(ImportRuleCtx& ctx,
                                            const ModuleItem* item,
                                            std::string_view pkg_name) {
  auto name = item->import_item.item_name;
  if (WildcardClaimOrigin(ctx, name) ==
      ExplicitImportOrigin(ctx, pkg_name, name)) {
    return false;
  }
  ctx.diag.Error(item->loc,
                 std::format("explicit import of '{}::{}' is illegal because "
                             "'{}' was already referenced through a wildcard "
                             "package import",
                             pkg_name, name, name),
                 Subclause("26.5"));
  return true;
}

bool ReportImportOfNoCandidate(ImportRuleCtx& ctx, const ModuleItem* item,
                               std::string_view pkg_name) {
  auto name = item->import_item.item_name;
  bool candidate = pkg_name == "std"
                       ? StdPackageMemberNamed(name).has_value()
                       : PackageProvidesName(ctx.unit, ctx.pkg_provided_names,
                                             pkg_name, name);
  if (candidate) return false;
  ctx.diag.Error(item->loc,
                 std::format("explicit import of '{}::{}', which package '{}' "
                             "neither declares nor exports",
                             pkg_name, name, pkg_name),
                 Subclause("26.3"));
  return true;
}

void HandleExplicitImport(ImportRuleCtx& ctx, const ModuleItem* item,
                          std::string_view pkg_name) {
  auto name = item->import_item.item_name;
  if (ReportImportOfNoCandidate(ctx, item, pkg_name)) return;
  if (CheckAgainstEarlierExplicitImport(ctx, item, pkg_name)) return;
  if (ctx.seen_decls.count(name)) {
    if (ctx.wildcard_claimed.find(name) != ctx.wildcard_claimed.end()) {
      if (ReportExplicitImportAfterWildcardClaim(ctx, item, pkg_name)) return;
    } else {
      ctx.diag.Error(item->loc,
                     std::format("explicit import of '{}::{}' collides with "
                                 "existing declaration of '{}'",
                                 pkg_name, name, name),
                     Subclause("26.3"));
      return;
    }
  }
  ctx.explicit_imports[name] = {pkg_name, item->loc};
  ctx.seen_decls.insert(name);
}

bool ReportImportBeforePackage(ImportRuleCtx& ctx, const ModuleItem* item,
                               std::string_view pkg_name) {
  for (const auto* pkg : ctx.unit->packages) {
    if (pkg->name != pkg_name || PrecedesInText(pkg->range.start, item->loc)) {
      continue;
    }
    ctx.diag.Error(item->loc,
                   std::format("import from package '{}', which is declared "
                               "after the scope importing it; a package must "
                               "be declared before any scope that imports "
                               "from it",
                               pkg_name),
                   Subclause("26.3"));
    return true;
  }
  return false;
}

void HandleImportDecl(ImportRuleCtx& ctx, const ModuleItem* item) {
  auto pkg_name = item->import_item.package_name;
  if (!PackageDeclared(ctx.unit, pkg_name)) {
    ctx.diag.Error(item->loc,
                   std::format("import from unknown package '{}'; the package "
                               "must be declared before any scope that imports "
                               "from it",
                               pkg_name),
                   Subclause("26.3"));
    return;
  }
  if (ReportImportBeforePackage(ctx, item, pkg_name)) return;
  if (item->import_item.is_wildcard) {
    if (std::find(ctx.wildcard_packages.begin(), ctx.wildcard_packages.end(),
                  pkg_name) == ctx.wildcard_packages.end()) {
      ctx.wildcard_packages.push_back(pkg_name);
    }
    return;
  }
  HandleExplicitImport(ctx, item, pkg_name);
}

void ProcessImportRuleRefs(ImportRuleCtx& ctx, const std::vector<Expr*>& refs) {
  for (Expr* ref : refs) ProcessImportRuleRef(ctx, ref);
}

void HandleImportRuleItem(ImportRuleCtx& ctx, const ModuleItem* item);

void HandleGenerateBlockImportRules(ImportRuleCtx& outer,
                                    const std::vector<ModuleItem*>& items,
                                    std::string_view genvar) {
  std::unordered_map<std::string_view, std::pair<std::string_view, SourceLoc>>
      explicit_imports;
  std::vector<std::string_view> wildcard_packages;
  std::unordered_map<std::string_view, SourceLoc> wildcard_claimed;
  std::unordered_set<std::string_view> seen_decls;
  OuterBoundRefs outer_bound;
  if (!genvar.empty()) seen_decls.insert(genvar);
  ImportRuleCtx ctx{
      outer.diag,       outer.unit,        outer.pkg_provided_names,
      explicit_imports, wildcard_packages, wildcard_claimed,
      seen_decls,       outer_bound,       &outer};
  for (const auto* item : items) HandleImportRuleItem(ctx, item);
}

void HandleSubroutineImportRules(ImportRuleCtx& outer, const ModuleItem* item) {
  TrackImportRuleDecl(outer, item->name, item->loc);
  std::unordered_map<std::string_view, std::pair<std::string_view, SourceLoc>>
      explicit_imports;
  std::vector<std::string_view> wildcard_packages;
  std::unordered_map<std::string_view, SourceLoc> wildcard_claimed;
  std::unordered_set<std::string_view> seen_decls{item->name};
  OuterBoundRefs outer_bound;
  for (const FunctionArg& arg : item->func_args) seen_decls.insert(arg.name);
  ImportRuleCtx ctx{
      outer.diag,       outer.unit,        outer.pkg_provided_names,
      explicit_imports, wildcard_packages, wildcard_claimed,
      seen_decls,       outer_bound,       &outer};
  for (const Stmt* s : item->func_body_stmts) {
    if (s->kind == StmtKind::kBlockItemDecl) {
      HandleImportRuleItem(ctx, s->decl_item);
      continue;
    }
    std::vector<Expr*> refs;
    WalkStmtIdents(s, refs);
    ProcessImportRuleRefs(ctx, refs);
    if (s->kind == StmtKind::kVarDecl) {
      TrackImportRuleDecl(ctx, s->var_name, s->range.start);
    }
  }
}

std::string_view GenerateLoopVariable(const ModuleItem* item) {
  const Stmt* init = item->gen_init;
  if (init == nullptr) return {};
  if (!init->var_name.empty()) return init->var_name;
  if (init->lhs != nullptr && init->lhs->kind == ExprKind::kIdentifier) {
    return init->lhs->text;
  }
  return {};
}

void HandleGenerateImportRules(ImportRuleCtx& ctx, const ModuleItem* item) {
  TrackImportRuleDecl(ctx, item->name, item->loc);
  HandleGenerateBlockImportRules(ctx, item->gen_body,
                                 GenerateLoopVariable(item));
  if (item->gen_else != nullptr) HandleImportRuleItem(ctx, item->gen_else);
  for (const auto& ci : item->gen_case_items) {
    HandleGenerateBlockImportRules(ctx, ci.body, {});
  }
}

void HandleImportRuleItem(ImportRuleCtx& ctx, const ModuleItem* item) {
  switch (item->kind) {
    case ModuleItemKind::kImportDecl:
      HandleImportDecl(ctx, item);
      break;
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
    case ModuleItemKind::kGenerateFor:
      HandleGenerateImportRules(ctx, item);
      break;
    case ModuleItemKind::kInitialBlock:
    case ModuleItemKind::kFinalBlock:
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock: {
      std::vector<Expr*> refs;
      WalkStmtIdents(item->body, refs);
      ProcessImportRuleRefs(ctx, refs);
      break;
    }
    case ModuleItemKind::kContAssign: {
      std::vector<Expr*> refs;
      WalkExprIdents(item->assign_lhs, refs);
      WalkExprIdents(item->assign_rhs, refs);
      ProcessImportRuleRefs(ctx, refs);
      break;
    }
    case ModuleItemKind::kModuleInst:
      TrackImportRuleDecl(ctx, item->inst_name, item->loc);
      break;
    case ModuleItemKind::kGateInst:
    case ModuleItemKind::kUdpInst:
      TrackImportRuleDecl(ctx, item->gate_inst_name, item->loc);
      break;
    case ModuleItemKind::kClassDecl:
      if (item->class_decl) {
        TrackImportRuleDecl(ctx, item->class_decl->name, item->loc);
      }
      break;
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
      if (item->method_class.empty()) {
        HandleSubroutineImportRules(ctx, item);
      } else {
        TrackImportRuleDecl(ctx, item->name, item->loc);
      }
      break;
    default:
      TrackImportRuleDecl(ctx, item->name, item->loc);
      auto track_literals = [&](std::string_view, const DataType& type) {
        for (const auto& em : type.enum_members)
          TrackImportRuleDecl(ctx, em.name, item->loc);
      };
      ForEachEnumTypeIn(item->typedef_type, track_literals);
      ForEachEnumTypeIn(item->data_type, track_literals);
      if (item->init_expr) {
        std::vector<Expr*> refs;
        WalkExprIdents(item->init_expr, refs);
        ProcessImportRuleRefs(ctx, refs);
      }
      break;
  }
}

void SeedImportRuleSeenDecls(const ModuleDecl* decl,
                             std::unordered_set<std::string_view>& seen_decls) {
  for (const auto& port : decl->ports) {
    if (!port.name.empty()) seen_decls.insert(port.name);
  }
  for (const auto& [pname, pval] : decl->params) {
    if (!pname.empty()) seen_decls.insert(pname);
  }
}

}  // namespace

void Elaborator::ValidatePackageImportRules(const ModuleDecl* decl) {
  explicit_imports_.clear();
  wildcard_packages_.clear();
  wildcard_claimed_.clear();

  wildcard_packages_.push_back("std");

  std::unordered_set<std::string_view> seen_decls;
  SeedImportRuleSeenDecls(decl, seen_decls);
  OuterBoundRefs outer_bound;

  std::vector<std::string_view> body_wildcards;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kImportDecl &&
        item->import_item.is_wildcard) {
      body_wildcards.push_back(item->import_item.package_name);
    }
  }
  const LateImportCheck kLate{
      body_wildcards,
      [this](std::string_view n) { return IsNameInModuleScope(n); },
      [this, decl](std::string_view n) {
        return UnitDeclaresData(unit_, n, decl->range.start);
      },
      [this](std::string_view n) { return IsDeclaredNameForRhs(n); }};

  ImportRuleCtx ctx{diag_,
                    unit_,
                    pkg_provided_names_,
                    explicit_imports_,
                    wildcard_packages_,
                    wildcard_claimed_,
                    seen_decls,
                    outer_bound,
                    nullptr,
                    &kLate};

  for (const auto* item : decl->items) HandleImportRuleItem(ctx, item);
}

}  // namespace delta
