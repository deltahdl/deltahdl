#include <algorithm>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {

struct ScopeWalk {
  std::vector<std::pair<std::string_view, SourceLoc>> block_labels;
  std::unordered_set<std::string_view> local_names;
  std::vector<std::pair<std::string_view, SourceLoc>> proc_lhs;
  // §12.7.1: control variables declared in a for-loop header are local to the
  // loop's implicit block. This stack holds the names currently in scope while
  // walking a loop's sub-statements, so assignments to them are not mistaken
  // for writes to an undeclared identifier and the names never leak outward.
  std::vector<std::string_view> active_loop_vars;
};

// §12.7.1: a for loop whose header declares its control variables (e.g.
// `for (int i = 0; ...)`) creates an implicit block; those variables are local
// to the loop and visible only in its condition, step, and body. Pushes each
// such name onto the active-loop-var stack and returns how many were pushed so
// the caller can pop them once the loop's sub-statements have been walked.
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

void CollectScopeWalk(const Stmt* s, ScopeWalk& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlock && !s->label.empty()) {
    out.block_labels.emplace_back(s->label, s->range.start);
  }
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
  for (const auto* sub : s->stmts) CollectScopeWalk(sub, out);
  for (const auto* sub : s->fork_stmts) CollectScopeWalk(sub, out);
  CollectScopeWalk(s->then_branch, out);
  CollectScopeWalk(s->else_branch, out);
  CollectScopeWalk(s->body, out);
  for (const auto& ci : s->case_items) CollectScopeWalk(ci.body, out);

  // §12.7.1: walk the for-loop's init, step, and body with the locally declared
  // control variables in scope, then drop them so they do not leak outward.
  size_t pushed = PushTypedForInitVars(s, out);
  for (const auto* fi : s->for_inits) CollectScopeWalk(fi, out);
  for (const auto* fs : s->for_steps) CollectScopeWalk(fs, out);
  CollectScopeWalk(s->for_body, out);
  out.active_loop_vars.resize(out.active_loop_vars.size() - pushed);
}

bool IsProcBodyItem(ModuleItemKind k) {
  return k == ModuleItemKind::kInitialBlock ||
         k == ModuleItemKind::kFinalBlock ||
         k == ModuleItemKind::kAlwaysBlock ||
         k == ModuleItemKind::kAlwaysCombBlock ||
         k == ModuleItemKind::kAlwaysFFBlock ||
         k == ModuleItemKind::kAlwaysLatchBlock;
}

// §8.30.1: a weak_reference's type parameter shall name a class type. The same
// rule already guards module-level variables, class members, and subroutine
// arguments; this walk extends it to procedural-block local variables, which
// are kVarDecl statements rather than ModuleItems.
void ValidateLocalWeakRefDecls(
    const Stmt* s, const std::unordered_set<std::string_view>& class_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl &&
      s->var_decl_type.type_name == "weak_reference" &&
      !s->var_decl_type.type_params.empty()) {
    const auto& tp = s->var_decl_type.type_params[0];
    if (tp.kind != DataTypeKind::kNamed ||
        class_names.count(tp.type_name) == 0) {
      diag.Error(s->range.start,
                 "weak_reference type parameter shall be a class type");
    }
  }
  for (const auto* sub : s->stmts)
    ValidateLocalWeakRefDecls(sub, class_names, diag);
  for (const auto* sub : s->fork_stmts)
    ValidateLocalWeakRefDecls(sub, class_names, diag);
  ValidateLocalWeakRefDecls(s->then_branch, class_names, diag);
  ValidateLocalWeakRefDecls(s->else_branch, class_names, diag);
  ValidateLocalWeakRefDecls(s->body, class_names, diag);
  ValidateLocalWeakRefDecls(s->for_body, class_names, diag);
  for (const auto* fi : s->for_inits)
    ValidateLocalWeakRefDecls(fi, class_names, diag);
  for (const auto* fs : s->for_steps)
    ValidateLocalWeakRefDecls(fs, class_names, diag);
  for (const auto& ci : s->case_items)
    ValidateLocalWeakRefDecls(ci.body, class_names, diag);
}

}  // namespace

namespace {

void WalkExprIdents(const Expr* e, std::vector<const Expr*>& out) {
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
  for (const auto* a : e->args) WalkExprIdents(a, out);
  for (const auto* el : e->elements) WalkExprIdents(el, out);
}

void WalkStmtIdents(const Stmt* s, std::vector<const Expr*>& out);

void WalkStmtScalarIdents(const Stmt* s, std::vector<const Expr*>& out) {
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
  for (const auto* e : s->wait_order_events) WalkExprIdents(e, out);
}

void WalkStmtCaseIdents(const Stmt* s, std::vector<const Expr*>& out) {
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns) WalkExprIdents(p, out);
    WalkStmtIdents(ci.body, out);
  }
  for (const auto& [w, body] : s->randcase_items) {
    WalkExprIdents(w, out);
    WalkStmtIdents(body, out);
  }
}

void WalkStmtChildIdents(const Stmt* s, std::vector<const Expr*>& out) {
  for (const auto* sub : s->stmts) WalkStmtIdents(sub, out);
  for (const auto* sub : s->fork_stmts) WalkStmtIdents(sub, out);
  WalkStmtIdents(s->then_branch, out);
  WalkStmtIdents(s->else_branch, out);
  WalkStmtIdents(s->body, out);
  WalkStmtIdents(s->for_body, out);
  for (const auto* fi : s->for_inits) WalkStmtIdents(fi, out);
  for (const auto* fs : s->for_steps) WalkStmtIdents(fs, out);
  WalkStmtIdents(s->assert_pass_stmt, out);
  WalkStmtIdents(s->assert_fail_stmt, out);
}

void WalkStmtIdents(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  WalkStmtScalarIdents(s, out);
  WalkStmtCaseIdents(s, out);
  WalkStmtChildIdents(s, out);
}

bool PackageDeclared(const CompilationUnit* unit, std::string_view pkg_name) {
  if (pkg_name == "std") return true;
  for (const auto* pkg : unit->packages) {
    if (pkg->name == pkg_name) return true;
  }
  return false;
}

void PopulatePackageProvidedNames(const CompilationUnit* unit,
                                  std::string_view pkg_name,
                                  std::unordered_set<std::string_view>& names) {
  for (const auto* pkg : unit->packages) {
    if (pkg->name != pkg_name) continue;
    for (const auto* pi : pkg->items) {
      if (!pi->name.empty()) names.insert(pi->name);
      if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
          !pi->class_decl->name.empty()) {
        names.insert(pi->class_decl->name);
      }
    }
  }
}

bool PackageProvidesName(
    const CompilationUnit* unit,
    std::unordered_map<std::string_view, std::unordered_set<std::string_view>>&
        provided_cache,
    std::string_view pkg_name, std::string_view name) {
  auto it = provided_cache.find(pkg_name);
  if (it == provided_cache.end()) {
    PopulatePackageProvidedNames(unit, pkg_name, provided_cache[pkg_name]);
    it = provided_cache.find(pkg_name);
  }
  return it->second.count(name) != 0;
}

// Mutable state shared across the import-rule checking helpers below. Holds
// references to the Elaborator members and per-call locals so the phases can be
// expressed as free functions without changing behavior.
struct ImportRuleCtx {
  DiagEngine& diag;
  const CompilationUnit* unit;
  std::unordered_map<std::string_view, std::unordered_set<std::string_view>>&
      pkg_provided_names;
  std::unordered_map<std::string_view, std::pair<std::string_view, SourceLoc>>&
      explicit_imports;
  std::vector<std::string_view>& wildcard_packages;
  std::unordered_map<std::string_view, SourceLoc>& wildcard_claimed;
  std::unordered_set<std::string_view>& seen_decls;
};

void TrackImportRuleDecl(ImportRuleCtx& ctx, std::string_view name,
                         SourceLoc loc) {
  if (name.empty()) return;
  auto wit = ctx.wildcard_claimed.find(name);
  if (wit != ctx.wildcard_claimed.end()) {
    ctx.diag.Error(loc,
                   std::format("declaration of '{}' follows a reference "
                               "resolved through a wildcard package import",
                               name));
  }
  ctx.seen_decls.insert(name);
}

void ProcessImportRuleRef(ImportRuleCtx& ctx, const Expr* e) {
  auto name = e->text;
  if (name.empty()) return;
  if (ctx.seen_decls.count(name)) return;
  std::vector<std::string_view> providers;
  for (auto pkg : ctx.wildcard_packages) {
    if (PackageProvidesName(ctx.unit, ctx.pkg_provided_names, pkg, name)) {
      providers.push_back(pkg);
    }
  }
  if (providers.size() > 1) {
    ctx.diag.Error(
        e->range.start,
        std::format("reference to '{}' is ambiguous between wildcard "
                    "imports of packages '{}' and '{}'",
                    name, providers[0], providers[1]));
    return;
  }
  if (providers.size() == 1) {
    ctx.wildcard_claimed[name] = e->range.start;
    ctx.seen_decls.insert(name);
  }
}

void HandleExplicitImport(ImportRuleCtx& ctx, const ModuleItem* item,
                          std::string_view pkg_name) {
  auto name = item->import_item.item_name;
  auto eit = ctx.explicit_imports.find(name);
  if (eit != ctx.explicit_imports.end()) {
    if (eit->second.first == pkg_name) return;
    ctx.diag.Error(
        item->loc,
        std::format("explicit import of '{}::{}' conflicts with earlier "
                    "explicit import from '{}'",
                    pkg_name, name, eit->second.first));
    return;
  }
  if (ctx.seen_decls.count(name)) {
    if (ctx.wildcard_claimed.find(name) != ctx.wildcard_claimed.end()) {
      ctx.diag.Error(
          item->loc,
          std::format("explicit import of '{}::{}' is illegal because "
                      "'{}' was already referenced through a wildcard "
                      "package import",
                      pkg_name, name, name));
    } else {
      ctx.diag.Error(item->loc,
                     std::format("explicit import of '{}::{}' collides with "
                                 "existing declaration of '{}'",
                                 pkg_name, name, name));
    }
    return;
  }
  ctx.explicit_imports[name] = {pkg_name, item->loc};
  ctx.seen_decls.insert(name);
}

void HandleImportDecl(ImportRuleCtx& ctx, const ModuleItem* item) {
  auto pkg_name = item->import_item.package_name;
  if (!PackageDeclared(ctx.unit, pkg_name)) {
    ctx.diag.Error(item->loc,
                   std::format("import from unknown package '{}'; the package "
                               "must be declared before any scope that imports "
                               "from it",
                               pkg_name));
    return;
  }
  if (item->import_item.is_wildcard) {
    if (std::find(ctx.wildcard_packages.begin(), ctx.wildcard_packages.end(),
                  pkg_name) == ctx.wildcard_packages.end()) {
      ctx.wildcard_packages.push_back(pkg_name);
    }
    return;
  }
  HandleExplicitImport(ctx, item, pkg_name);
}

void ProcessImportRuleRefs(ImportRuleCtx& ctx,
                           const std::vector<const Expr*>& refs) {
  for (const auto* e : refs) ProcessImportRuleRef(ctx, e);
}

void HandleImportRuleItem(ImportRuleCtx& ctx, const ModuleItem* item) {
  switch (item->kind) {
    case ModuleItemKind::kImportDecl:
      HandleImportDecl(ctx, item);
      break;
    case ModuleItemKind::kInitialBlock:
    case ModuleItemKind::kFinalBlock:
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock: {
      std::vector<const Expr*> refs;
      WalkStmtIdents(item->body, refs);
      ProcessImportRuleRefs(ctx, refs);
      break;
    }
    case ModuleItemKind::kContAssign: {
      std::vector<const Expr*> refs;
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
    default:
      TrackImportRuleDecl(ctx, item->name, item->loc);
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

  ImportRuleCtx ctx{diag_,
                    unit_,
                    pkg_provided_names_,
                    explicit_imports_,
                    wildcard_packages_,
                    wildcard_claimed_,
                    seen_decls};

  // §26.3: a wildcard import makes its names candidates throughout the entire
  // scope, including for references that textually precede the import. Gather
  // every (declared) wildcard package up front so such references resolve --
  // and, when two wildcard imports supply the same name, are reported as
  // ambiguous. Only the package list is pre-seeded here; claim/decl ordering
  // is still driven by the textual pass below.
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_wildcard) continue;
    auto pkg = item->import_item.package_name;
    if (!PackageDeclared(unit_, pkg)) continue;
    if (std::find(wildcard_packages_.begin(), wildcard_packages_.end(), pkg) ==
        wildcard_packages_.end()) {
      wildcard_packages_.push_back(pkg);
    }
  }

  for (const auto* item : decl->items) HandleImportRuleItem(ctx, item);
}

void Elaborator::ValidateScopeRules(const ModuleDecl* decl) {
  ScopeWalk walk;
  for (const auto* item : decl->items) {
    if (IsProcBodyItem(item->kind)) {
      CollectScopeWalk(item->body, walk);
      ValidateLocalWeakRefDecls(item->body, class_names_, diag_);
    }
  }
  for (const auto& [label, loc] : walk.block_labels) {
    if (!declared_names_.insert(label).second) {
      diag_.Error(loc, std::format("redeclaration of '{}'", label));
    }
  }
  for (const auto& [name, loc] : walk.proc_lhs) {
    if (walk.local_names.count(name)) continue;
    if (IsNameInModuleScope(name)) continue;
    diag_.Error(loc, std::format("undeclared identifier '{}'", name));
  }
}

namespace {

// A built-in data-type keyword (logic, bit, int, ...) parsed in expression
// position — e.g. the type argument of `$bits(logic [7:0])` — is materialized
// as a `kIdentifier` node carrying the keyword text (see
// ParseCastOrTypedPattern). Such a node is a type reference, not a value read,
// so it must never be checked against the value namespace. Mirrors
// IsCastTypeToken in the expression parser.
bool IsBuiltinTypeKeyword(std::string_view name) {
  static constexpr std::string_view kTypeKeywords[] = {
      "logic",   "bit",      "byte",   "int",       "shortint", "longint",
      "integer", "reg",      "real",   "shortreal", "realtime", "time",
      "signed",  "unsigned", "string", "const",     "void"};
  for (auto kw : kTypeKeywords) {
    if (name == kw) return true;
  }
  return false;
}

// Collects standalone identifier operands of `e`, deliberately NOT descending
// into member-access subtrees (so the base of `a.b`, `s.field`, `$root.x`, or
// `pkg::x` is never collected) and skipping scope-prefixed identifiers. Only
// the plain `kIdentifier` reads that must resolve to a local declaration
// survive.
void CollectBareIdents(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess) return;
  if (e->kind == ExprKind::kIdentifier) {
    if (e->scope_prefix.empty() && !IsBuiltinTypeKeyword(e->text)) {
      out.push_back(e);
    }
    return;
  }
  CollectBareIdents(e->lhs, out);
  CollectBareIdents(e->rhs, out);
  CollectBareIdents(e->base, out);
  CollectBareIdents(e->index, out);
  CollectBareIdents(e->index_end, out);
  CollectBareIdents(e->condition, out);
  CollectBareIdents(e->true_expr, out);
  CollectBareIdents(e->false_expr, out);
  CollectBareIdents(e->repeat_count, out);
  CollectBareIdents(e->with_expr, out);
  for (const auto* a : e->args) CollectBareIdents(a, out);
  for (const auto* el : e->elements) CollectBareIdents(el, out);
}

// True when the module imports any name or contains a generate construct, in
// which case a bare identifier may legally resolve to an imported name or a
// generated/genvar name the elaborated module's symbol table does not list.
// Skipping such modules keeps the unresolved-reference check free of false
// positives.
bool ModuleSkipsUnresolvedCheck(const ModuleDecl* decl,
                                const RtlirModule* mod) {
  // Every module carries an auto-injected `import std::*` (see
  // elaborator_module.cpp); that implicit wildcard brings in only the small,
  // known std package and must not disable the check. Any *other* import means
  // a bare name may legally resolve to an imported package member the module
  // symbol table does not list, so skip such modules to avoid false positives.
  for (const auto& imp : mod->imports) {
    if (imp.package_name != "std" || !imp.is_wildcard) return true;
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kGenerateFor ||
        item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase) {
      return true;
    }
  }
  return false;
}

// §6.16/§6.22.5: a string and an integral or real type are type-incompatible —
// no implicit or explicit cast bridges them — so a direct procedural assignment
// between a string variable and a numeric variable is an error. The check is
// restricted to the string<->numeric pair: it is the residual §6.22.5 case that
// carries no width/signedness nuance, so flagging it stays free of the false
// positives that a general residual check would raise on integral/real
// conversions (which are assignment-compatible).
bool IsStringKind(DataTypeKind k) { return k == DataTypeKind::kString; }

bool IsNumericKind(DataTypeKind k) {
  return IsIntegralType(k) || k == DataTypeKind::kReal ||
         k == DataTypeKind::kShortreal || k == DataTypeKind::kRealtime;
}

// Leaf check for a single statement: flag a blocking/nonblocking assign whose
// two sides are identifiers resolving to a string and a numeric var.
void CheckStringNumericAssignStmt(
    const Stmt* s,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    DiagEngine& diag) {
  if (s->kind != StmtKind::kBlockingAssign &&
      s->kind != StmtKind::kNonblockingAssign) {
    return;
  }
  if (!s->lhs || s->lhs->kind != ExprKind::kIdentifier || !s->rhs ||
      s->rhs->kind != ExprKind::kIdentifier) {
    return;
  }
  auto lit = var_types.find(s->lhs->text);
  auto rit = var_types.find(s->rhs->text);
  if (lit == var_types.end() || rit == var_types.end()) return;
  bool incompatible =
      (IsStringKind(lit->second) && IsNumericKind(rit->second)) ||
      (IsStringKind(rit->second) && IsNumericKind(lit->second));
  if (incompatible) {
    diag.Error(s->range.start,
               "type-incompatible assignment between string and numeric type");
  }
}

void CheckStringNumericAssigns(
    const Stmt* s,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    DiagEngine& diag) {
  if (!s) return;
  CheckStringNumericAssignStmt(s, var_types, diag);
  for (const auto* sub : s->stmts)
    CheckStringNumericAssigns(sub, var_types, diag);
  for (const auto* sub : s->fork_stmts)
    CheckStringNumericAssigns(sub, var_types, diag);
  CheckStringNumericAssigns(s->then_branch, var_types, diag);
  CheckStringNumericAssigns(s->else_branch, var_types, diag);
  CheckStringNumericAssigns(s->body, var_types, diag);
  CheckStringNumericAssigns(s->for_body, var_types, diag);
  for (const auto* fi : s->for_inits)
    CheckStringNumericAssigns(fi, var_types, diag);
  for (const auto* fs : s->for_steps)
    CheckStringNumericAssigns(fs, var_types, diag);
  for (const auto& ci : s->case_items)
    CheckStringNumericAssigns(ci.body, var_types, diag);
}

// Over-approximated set of names that are local to a procedural block: block
// (begin/end) variable declarations, for-loop control variables, and foreach
// index variables. Collected flat across the whole block tree without tracking
// scope boundaries — that can only ever SUPPRESS a diagnostic, never raise one,
// so a missed boundary is always safe.
void CollectProcLocalNames(const Stmt* s,
                           std::unordered_set<std::string_view>& names) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    names.insert(s->var_name);
  }
  for (auto v : s->foreach_vars) names.insert(v);
  for (const auto* sub : s->stmts) CollectProcLocalNames(sub, names);
  for (const auto* sub : s->fork_stmts) CollectProcLocalNames(sub, names);
  CollectProcLocalNames(s->then_branch, names);
  CollectProcLocalNames(s->else_branch, names);
  CollectProcLocalNames(s->body, names);
  CollectProcLocalNames(s->for_body, names);
  for (const auto* fi : s->for_inits) {
    if (fi && fi->lhs && fi->lhs->kind == ExprKind::kIdentifier) {
      names.insert(fi->lhs->text);
    }
    CollectProcLocalNames(fi, names);
  }
  for (const auto* fs : s->for_steps) CollectProcLocalNames(fs, names);
  for (const auto& ci : s->case_items) CollectProcLocalNames(ci.body, names);
}

// Collects the RHS Expr of every procedural blocking/nonblocking assignment
// whose ENTIRE rhs is a single bare identifier that is not a literal (null/$),
// a builtin type keyword, or a block-local name. The caller then rejects any
// that resolve to no declaration. Restricting to a single-identifier rhs is
// what keeps this free of false positives: every other identifier-shaped rhs
// primary that is NOT a value read (a call/tag/stream-size operand, a
// member/scoped reference) only ever appears INSIDE a larger expression, so it
// is never the whole rhs.
void CollectProcSingleIdentRhs(
    const Stmt* s, const std::unordered_set<std::string_view>& locals,
    std::vector<const Expr*>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    const Expr* r = s->rhs;
    if (r && r->kind == ExprKind::kIdentifier && r->scope_prefix.empty() &&
        r->text != "null" && r->text != "$" && !IsBuiltinTypeKeyword(r->text) &&
        locals.count(r->text) == 0) {
      out.push_back(r);
    }
  }
  for (const auto* sub : s->stmts) CollectProcSingleIdentRhs(sub, locals, out);
  for (const auto* sub : s->fork_stmts)
    CollectProcSingleIdentRhs(sub, locals, out);
  CollectProcSingleIdentRhs(s->then_branch, locals, out);
  CollectProcSingleIdentRhs(s->else_branch, locals, out);
  CollectProcSingleIdentRhs(s->body, locals, out);
  CollectProcSingleIdentRhs(s->for_body, locals, out);
  for (const auto* fi : s->for_inits)
    CollectProcSingleIdentRhs(fi, locals, out);
  for (const auto* fs : s->for_steps)
    CollectProcSingleIdentRhs(fs, locals, out);
  for (const auto& ci : s->case_items)
    CollectProcSingleIdentRhs(ci.body, locals, out);
}

// §6.5/§23.6: rejects an unresolved bare identifier read on a procedural
// assignment RHS. Block-local names are gathered first so the single-identifier
// check never flags a block-scoped declaration; `declared` resolves a name
// against the module/CU scope.
template <typename Pred>
void ReportProcUnresolved(const ModuleDecl* decl, Pred declared,
                          DiagEngine& diag) {
  std::unordered_set<std::string_view> locals;
  for (const auto* item : decl->items) {
    if (IsProcBodyItem(item->kind)) CollectProcLocalNames(item->body, locals);
  }
  std::vector<const Expr*> refs;
  for (const auto* item : decl->items) {
    if (IsProcBodyItem(item->kind)) {
      CollectProcSingleIdentRhs(item->body, locals, refs);
    }
  }
  for (const auto* e : refs) {
    if (declared(e->text)) continue;
    diag.Error(e->range.start,
               std::format("reference to unresolved identifier '{}'", e->text));
  }
}

// Collects the base identifier of every scope-resolution member access
// (`base::member`, marked is_scope_resolution by the parser) whose base is a
// plain identifier, recursing through the whole expression tree so nested forms
// (`a::b::c`, scope refs inside calls/concats) are reached. System scopes
// (`$unit::`, `$root.`) carry their prefix in scope_prefix and are skipped
// here.
void CollectScopeBases(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->is_scope_resolution && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier && e->lhs->scope_prefix.empty() &&
      !e->lhs->text.starts_with("$")) {
    out.push_back(e->lhs);
  }
  CollectScopeBases(e->lhs, out);
  CollectScopeBases(e->rhs, out);
  CollectScopeBases(e->base, out);
  CollectScopeBases(e->index, out);
  CollectScopeBases(e->index_end, out);
  CollectScopeBases(e->condition, out);
  CollectScopeBases(e->true_expr, out);
  CollectScopeBases(e->false_expr, out);
  CollectScopeBases(e->repeat_count, out);
  CollectScopeBases(e->with_expr, out);
  for (const auto* a : e->args) CollectScopeBases(a, out);
  for (const auto* el : e->elements) CollectScopeBases(el, out);
}

// Walks a procedural block, collecting scope-resolution bases from the RHS of
// every blocking/nonblocking assignment.
void CollectProcScopeBases(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CollectScopeBases(s->rhs, out);
  }
  for (const auto* sub : s->stmts) CollectProcScopeBases(sub, out);
  for (const auto* sub : s->fork_stmts) CollectProcScopeBases(sub, out);
  CollectProcScopeBases(s->then_branch, out);
  CollectProcScopeBases(s->else_branch, out);
  CollectProcScopeBases(s->body, out);
  CollectProcScopeBases(s->for_body, out);
  for (const auto* fi : s->for_inits) CollectProcScopeBases(fi, out);
  for (const auto* fs : s->for_steps) CollectProcScopeBases(fs, out);
  for (const auto& ci : s->case_items) CollectProcScopeBases(ci.body, out);
}

// §26.3: a scope-resolution prefix `base::` shall name a package (or a class /
// type, for static-member and type-scope access). `known` accepts those base
// names; "std" is the always-available built-in package. Any other base is an
// unresolved package or scope.
template <typename Pred>
void ReportUnknownScopeBases(const ModuleDecl* decl, Pred known,
                             DiagEngine& diag) {
  std::vector<const Expr*> bases;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CollectScopeBases(item->assign_rhs, bases);
    } else if (IsProcBodyItem(item->kind)) {
      CollectProcScopeBases(item->body, bases);
    }
  }
  for (const auto* b : bases) {
    if (b->text == "std" || b->text == "local" || known(b->text)) continue;
    diag.Error(
        b->range.start,
        std::format("reference to unresolved package or scope '{}'", b->text));
  }
}

// True when `n` names a known scope-resolution base: a compilation-unit scope
// name (package/class/interface), a module-local class or typedef, or a
// declared package (§26.3).
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
  // var_types_ records the bare name of every elaborated net and variable; the
  // remaining sets cover names that are not signals (typedefs, nettypes,
  // sequences, compilation-unit names) but may still be read by name.
  return var_types_.count(name) != 0 || IsNameInModuleScope(name) ||
         typedefs_.count(name) != 0 || nettype_names_.count(name) != 0 ||
         sequence_names_.count(name) != 0 ||
         assoc_typedef_names_.count(name) != 0 ||
         cu_scope_names_.count(name) != 0;
}

void Elaborator::ValidateUnresolvedReferences(const ModuleDecl* decl,
                                              const RtlirModule* mod) {
  if (!mod) return;

  // §6.16/§6.22.5: string<->numeric procedural assignments are
  // type-incompatible independent of any package imports, so check them before
  // the import-aware bare-name gate below (which skips modules with non-std
  // imports).
  for (const auto* item : decl->items) {
    if (IsProcBodyItem(item->kind)) {
      CheckStringNumericAssigns(item->body, var_types_, diag_);
    }
  }

  if (ModuleSkipsUnresolvedCheck(decl, mod)) return;

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    std::vector<const Expr*> refs;
    CollectBareIdents(item->assign_rhs, refs);
    for (const auto* e : refs) {
      if (IsDeclaredNameForRhs(e->text)) continue;
      diag_.Error(
          e->range.start,
          std::format("reference to unresolved identifier '{}'", e->text));
    }
  }

  ReportProcUnresolved(
      decl, [this](std::string_view n) { return IsDeclaredNameForRhs(n); },
      diag_);

  // §26.3: a `pkg::x` scope prefix must name a known package (or a class/type
  // for static-member / type-scope access). cu_scope_names_ holds packages,
  // classes, and interfaces; class_names_ and typedefs_ cover module-local
  // classes and type names.
  ReportUnknownScopeBases(
      decl,
      [this](std::string_view n) {
        return IsKnownScopeBase(n, cu_scope_names_, class_names_, typedefs_,
                                unit_);
      },
      diag_);
}

// §23.9/§24.3: true when a lexically enclosing scope declares `name`.
static bool NameInEnclosingScope(
    const std::vector<std::unordered_set<std::string_view>>& scopes,
    std::string_view name) {
  for (const auto& scope : scopes) {
    if (scope.count(name)) return true;
  }
  return false;
}

bool Elaborator::IsNameInModuleScope(std::string_view name) const {
  if (declared_names_.count(name)) return true;
  if (ansi_port_names_.count(name)) return true;
  if (non_ansi_complete_ports_.count(name)) return true;
  if (non_ansi_partial_ports_.count(name)) return true;
  if (const_names_.count(name)) return true;
  if (enum_member_names_.count(name)) return true;
  if (specparam_names_.count(name)) return true;
  if (class_names_.count(name)) return true;
  if (class_var_names_.count(name)) return true;
  if (task_names_.count(name)) return true;
  if (let_names_.count(name)) return true;
  if (func_decls_.count(name)) return true;
  if (interface_inst_types_.count(name)) return true;
  if (checker_inst_names_.count(name)) return true;
  // §23.9/§24.3: a lexically nested module/program/interface also sees names
  // declared in the scopes that textually enclose it.
  if (NameInEnclosingScope(enclosing_scope_names_, name)) return true;
  return false;
}

std::unordered_set<std::string_view> Elaborator::CaptureCurrentScopeNames()
    const {
  std::unordered_set<std::string_view> scope;
  scope.insert(declared_names_.begin(), declared_names_.end());
  scope.insert(const_names_.begin(), const_names_.end());
  scope.insert(enum_member_names_.begin(), enum_member_names_.end());
  scope.insert(specparam_names_.begin(), specparam_names_.end());
  scope.insert(class_names_.begin(), class_names_.end());
  scope.insert(class_var_names_.begin(), class_var_names_.end());
  scope.insert(task_names_.begin(), task_names_.end());
  scope.insert(let_names_.begin(), let_names_.end());
  scope.insert(ansi_port_names_.begin(), ansi_port_names_.end());
  scope.insert(non_ansi_complete_ports_.begin(),
               non_ansi_complete_ports_.end());
  scope.insert(checker_inst_names_.begin(), checker_inst_names_.end());
  for (const auto& [name, kind] : var_types_) scope.insert(name);
  for (const auto& [name, item] : func_decls_) scope.insert(name);
  for (const auto& [name, width] : non_ansi_partial_ports_) scope.insert(name);
  for (const auto& [name, type] : interface_inst_types_) scope.insert(name);
  for (const auto& [name, type] : typedefs_) scope.insert(name);
  return scope;
}

namespace {

bool ForwardTypedefHasDefinition(const ModuleDecl* decl,
                                 const ModuleItem* item) {
  for (const auto* other : decl->items) {
    if (other == item) continue;
    if (other->kind == ModuleItemKind::kTypedef && other->name == item->name &&
        other->typedef_type.kind != DataTypeKind::kImplicit) {
      return true;
    }
    if (other->kind == ModuleItemKind::kClassDecl && other->class_decl &&
        other->class_decl->name == item->name) {
      return true;
    }
  }
  return false;
}

void ScanForwardScopePrefix(const ModuleDecl* decl, std::string_view scope,
                            bool& is_forward_in_scope,
                            bool& resolves_to_class) {
  for (const auto* other : decl->items) {
    if (other->kind == ModuleItemKind::kTypedef && other->name == scope &&
        other->typedef_type.kind == DataTypeKind::kImplicit) {
      is_forward_in_scope = true;
    }
    if (other->kind == ModuleItemKind::kClassDecl && other->class_decl &&
        other->class_decl->name == scope) {
      resolves_to_class = true;
    }
  }
}

}  // namespace

void Elaborator::ValidateForwardTypedefsInScope(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kImplicit) continue;
    bool resolved = ForwardTypedefHasDefinition(decl, item);
    if (!resolved && class_names_.count(item->name) > 0) {
      resolved = true;
    }
    if (!resolved) {
      diag_.Error(item->loc,
                  std::format("forward typedef '{}' is never resolved by a "
                              "definition in the same scope",
                              item->name));
    }
  }
}

void Elaborator::ValidateForwardTypedefScopePrefix(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kNamed) continue;
    if (item->typedef_type.scope_name.empty()) continue;
    auto scope = item->typedef_type.scope_name;
    bool is_forward_in_scope = false;
    bool resolves_to_class = class_names_.count(scope) > 0;
    ScanForwardScopePrefix(decl, scope, is_forward_in_scope, resolves_to_class);
    if (!is_forward_in_scope) continue;
    if (!resolves_to_class) {
      diag_.Error(item->loc,
                  std::format("scope-resolution prefix '{}' of a typedef does "
                              "not resolve to a class",
                              scope));
    }
  }
}

}  // namespace delta
