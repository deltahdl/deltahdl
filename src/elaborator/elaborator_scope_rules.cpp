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
#include "elaborator/elaborator_scope_rules_names.h"
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

// §23.9: each begin-end block and each fork-join block -- named or unnamed --
// defines a new scope, and an identifier shall be used to declare only one item
// within a scope. Flags a second variable declaration that shares a name with
// an earlier one in the SAME statement list. Only the declarations that are
// direct children of one list are compared: a nested block is a distinct scope,
// so reusing a name there is legal shadowing rather than a redeclaration. The
// caller passes one scope's own statement list, and then descends so every
// nested block is checked against itself.
static void CheckOneBlockLocals(const std::vector<Stmt*>& block_stmts,
                                DiagEngine& diag) {
  std::unordered_set<std::string_view> block_locals;
  for (const auto* child : block_stmts) {
    if (!child || child->kind != StmtKind::kVarDecl || child->var_name.empty())
      continue;
    if (!block_locals.insert(child->var_name).second) {
      diag.Error(child->range.start,
                 std::format("redeclaration of '{}'", child->var_name),
                 Subclause("23.9"));
    }
  }
}

void CheckBlockLocalRedeclarations(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlock) CheckOneBlockLocals(s->stmts, diag);
  // §23.9 lists "fork-join blocks (named or unnamed)" among the elements that
  // define a new scope, beside "begin-end blocks (named or unnamed)". A
  // declaration written directly inside a fork lands in Stmt::fork_stmts on a
  // node whose kind is StmtKind::kFork, so that list is the fork-join block's
  // own scope and two declarations of one name in it are a redeclaration. The
  // list is checked on its own rather than merged into the enclosing block's,
  // because the fork-join block is a separate scope and a name reused there is
  // legal shadowing.
  if (s->kind == StmtKind::kFork) CheckOneBlockLocals(s->fork_stmts, diag);
  for (const auto* sub : s->stmts) CheckBlockLocalRedeclarations(sub, diag);
  for (const auto* sub : s->fork_stmts)
    CheckBlockLocalRedeclarations(sub, diag);
  CheckBlockLocalRedeclarations(s->then_branch, diag);
  CheckBlockLocalRedeclarations(s->else_branch, diag);
  CheckBlockLocalRedeclarations(s->body, diag);
  CheckBlockLocalRedeclarations(s->for_body, diag);
  for (const auto* fi : s->for_inits) CheckBlockLocalRedeclarations(fi, diag);
  for (const auto* fs : s->for_steps) CheckBlockLocalRedeclarations(fs, diag);
  for (const auto& ci : s->case_items)
    CheckBlockLocalRedeclarations(ci.body, diag);
}

// §8.30.1: a weak_reference's type parameter shall name a class type. The same
// rule already guards module-level variables, class members, and subroutine
// arguments; this walk extends it to procedural-block local variables, which
// are kVarDecl statements rather than ModuleItems.
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
                 "weak_reference type parameter shall be a class type",
                 Subclause("8.30.1"));
    }
  }
  for (const auto* sub : s->stmts)
    ValidateLocalWeakRefDecls(sub, typedefs, class_names, diag);
  for (const auto* sub : s->fork_stmts)
    ValidateLocalWeakRefDecls(sub, typedefs, class_names, diag);
  ValidateLocalWeakRefDecls(s->then_branch, typedefs, class_names, diag);
  ValidateLocalWeakRefDecls(s->else_branch, typedefs, class_names, diag);
  ValidateLocalWeakRefDecls(s->body, typedefs, class_names, diag);
  ValidateLocalWeakRefDecls(s->for_body, typedefs, class_names, diag);
  for (const auto* fi : s->for_inits)
    ValidateLocalWeakRefDecls(fi, typedefs, class_names, diag);
  for (const auto* fs : s->for_steps)
    ValidateLocalWeakRefDecls(fs, typedefs, class_names, diag);
  for (const auto& ci : s->case_items)
    ValidateLocalWeakRefDecls(ci.body, typedefs, class_names, diag);
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

// §26.5 / Table 26-1: the enumeration constants declared inside a package's
// enum become directly visible through a wildcard import just like any other
// package declaration (the FALSE/TRUE members of the clause's example package
// p). Each member name is registered so that a name supplied by two
// wildcard-imported packages is detected as ambiguous, not just the enum type
// name itself.
static void AddEnumMemberNames(const std::vector<EnumMember>& members,
                               std::unordered_set<std::string_view>& names) {
  for (const auto& em : members) {
    if (!em.name.empty()) names.insert(em.name);
  }
}

// The names one package item makes directly visible: its own name, the name of
// a class it declares, and any enumeration constants it brings, which may sit
// on a typedef's type or on a bare enum data declaration.
static void AddPackageItemNames(const ModuleItem* pi,
                                std::unordered_set<std::string_view>& names) {
  if (!pi->name.empty()) names.insert(pi->name);
  if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
      !pi->class_decl->name.empty()) {
    names.insert(pi->class_decl->name);
  }
  AddEnumMemberNames(pi->typedef_type.enum_members, names);
  AddEnumMemberNames(pi->data_type.enum_members, names);
}

void PopulatePackageProvidedNames(const CompilationUnit* unit,
                                  std::string_view pkg_name,
                                  std::unordered_set<std::string_view>& names) {
  for (const auto* pkg : unit->packages) {
    if (pkg->name != pkg_name) continue;
    for (const auto* pi : pkg->items) AddPackageItemNames(pi, names);
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
                               name),
                   Subclause("26.3"));
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
                    name, providers[0], providers[1]),
        Subclause("26.3"));
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
                    pkg_name, name, eit->second.first),
        Subclause("26.3"));
    return;
  }
  if (ctx.seen_decls.count(name)) {
    if (ctx.wildcard_claimed.find(name) != ctx.wildcard_claimed.end()) {
      // Table 26-1 of §26.5, row `import p::c;`, column "In a scope containing
      // a wildcard import of c": "The import of p::c makes any prior reference
      // to c illegal." §26.3 states the other three import-legality rules this
      // function enforces but not this one, and the worked example closing
      // §26.5 (`import q::*; wire a = c; import p::c;`) is this rule alone.
      ctx.diag.Error(
          item->loc,
          std::format("explicit import of '{}::{}' is illegal because "
                      "'{}' was already referenced through a wildcard "
                      "package import",
                      pkg_name, name, name),
          Subclause("26.5"));
    } else {
      ctx.diag.Error(item->loc,
                     std::format("explicit import of '{}::{}' collides with "
                                 "existing declaration of '{}'",
                                 pkg_name, name, name),
                     Subclause("26.3"));
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
                               pkg_name),
                   Subclause("26.3"));
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
      // §26.5 module m example: a net/variable/parameter declaration with an
      // initializer (e.g. `wire a = c;`) references names in that initializer.
      // Such a reference forces a wildcard import to claim the name just like a
      // procedural or continuous-assignment reference does, so a later
      // declaration or explicit import of the same name then conflicts. Track
      // the declared name first (so a self-referential initializer sees the
      // local decl), then process the initializer's references.
      TrackImportRuleDecl(ctx, item->name, item->loc);
      // §6.19: an enum declaration also introduces its member names into the
      // enclosing scope, so those names participate in import-collision
      // detection just like the enum type name. Register members from both a
      // typedef enum and a bare enum data declaration, mirroring how a
      // package's enum members are treated as wildcard-import candidates.
      for (const auto& em : item->typedef_type.enum_members) {
        TrackImportRuleDecl(ctx, em.name, item->loc);
      }
      for (const auto& em : item->data_type.enum_members) {
        TrackImportRuleDecl(ctx, em.name, item->loc);
      }
      if (item->init_expr) {
        std::vector<const Expr*> refs;
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
    if (IsProceduralItemKind(item->kind)) {
      CollectScopeWalk(item->body, walk);
      ValidateLocalWeakRefDecls(item->body, typedefs_, class_names_, diag_);
      CheckBlockLocalRedeclarations(item->body, diag_);
    }
  }
  for (const auto& [label, loc] : walk.block_labels) {
    if (!declared_names_.insert(label).second) {
      diag_.Error(loc, std::format("redeclaration of '{}'", label),
                  Subclause("23.9"));
    }
  }
  for (const auto& [name, loc] : walk.proc_lhs) {
    if (walk.local_names.count(name)) continue;
    if (IsNameInModuleScope(name)) continue;
    diag_.Error(loc, std::format("undeclared identifier '{}'", name),
                Subclause("23.9"));
  }
}

namespace {

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
               "type-incompatible assignment between string and numeric type",
               Subclause("6.16"));
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

// §23.9: reports every collected read that names no declaration the reference
// can reach.
template <typename Pred>
void ReportUnresolvedRefs(const std::vector<const Expr*>& refs, Pred declared,
                          DiagEngine& diag) {
  for (const auto* e : refs) {
    if (declared(e->text)) continue;
    diag.Error(e->range.start,
               std::format("reference to unresolved identifier '{}'", e->text),
               Subclause("23.9"));
  }
}

// §23.9: rejects an unresolved bare identifier read on a procedural assignment
// RHS. Block-local names are gathered first so a block-scoped declaration is
// never flagged; `declared` resolves a name against the module/CU scope.
template <typename Pred>
void ReportProcUnresolved(const ModuleDecl* decl, Pred declared,
                          DiagEngine& diag) {
  std::unordered_set<std::string_view> locals;
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      CollectProcLocalNames(item->body, locals);
  }
  std::vector<const Expr*> refs;
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      CollectProcRhsIdents(item->body, locals, refs);
    }
  }
  ReportUnresolvedRefs(refs, declared, diag);
}

// §23.9: rejects an unresolved bare identifier read in the initializer of a
// variable or net declaration. §6.8 writes the initializer as part of the
// declaration rather than as a statement, so no procedural walk reaches it, and
// `int q = v;` read a name the module does not declare with nothing said.
template <typename Pred>
void ReportDeclInitUnresolved(const ModuleDecl* decl, Pred declared,
                              DiagEngine& diag) {
  std::vector<const Expr*> refs;
  for (const auto* item : decl->items) {
    bool is_data_decl = item->kind == ModuleItemKind::kVarDecl ||
                        item->kind == ModuleItemKind::kNetDecl;
    if (!is_data_decl || item->init_expr == nullptr) continue;
    CollectBareIdents(item->init_expr, refs);
  }
  ReportUnresolvedRefs(refs, declared, diag);
}

// §23.9: rejects an unresolved bare identifier read in a task or function body.
// §23.9 lists a task and a function among the scopes an identifier is searched
// upward from, and rules that the search "shall stop at a module boundary" when
// the item is a variable, so a subroutine body is held to the boundary exactly
// as a procedural block of the same module is.
template <typename Pred>
void ReportSubroutineUnresolved(const ModuleDecl* decl, Pred declared,
                                DiagEngine& diag) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTaskDecl &&
        item->kind != ModuleItemKind::kFunctionDecl) {
      continue;
    }
    std::unordered_set<std::string_view> locals;
    CollectSubroutineLocalNames(item, locals);
    std::vector<const Expr*> refs;
    for (const auto* stmt : item->func_body_stmts) {
      CollectProcRhsIdents(stmt, locals, refs);
    }
    ReportUnresolvedRefs(refs, declared, diag);
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
    } else if (IsProceduralItemKind(item->kind)) {
      CollectProcScopeBases(item->body, bases);
    }
  }
  for (const auto* b : bases) {
    if (b->text == "std" || b->text == "local" || known(b->text)) continue;
    diag.Error(
        b->range.start,
        std::format("reference to unresolved package or scope '{}'", b->text),
        Subclause("26.3"));
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

// §26.3: an explicit import makes exactly its named symbol visible without a
// package qualifier. A bare read of such a symbol resolves, while a read of a
// package member that was NOT imported still falls through to the unresolved
// diagnostic.
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

// True where any of `pkgs` declares `name`. §26.3 makes every name a
// wildcard-imported package declares directly visible, so a bare read of one
// resolves without the package qualifier.
static bool AnyPackageProvidesName(
    const CompilationUnit* unit,
    std::unordered_map<std::string_view, std::unordered_set<std::string_view>>&
        provided_cache,
    const std::vector<std::string_view>& pkgs, std::string_view name) {
  for (auto pkg : pkgs) {
    if (PackageProvidesName(unit, provided_cache, pkg, name)) return true;
  }
  return false;
}

// Report every bare identifier read by a continuous assignment that names
// nothing visible in the module.
template <typename Declared>
static void ReportContAssignUnresolved(const ModuleDecl* decl,
                                       const Declared& declared,
                                       DiagEngine& diag) {
  std::vector<const Expr*> refs;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    CollectBareIdents(item->assign_rhs, refs);
  }
  ReportUnresolvedRefs(refs, declared, diag);
}

void Elaborator::ValidateUnresolvedReferences(const ModuleDecl* decl,
                                              const RtlirModule* mod) {
  if (!mod) return;

  // §6.16/§6.22.5: a string and an integral or real type are
  // type-incompatible whatever a module imports, so this check answers on its
  // own and is stated before the §23.9 reads below.
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      CheckStringNumericAssigns(item->body, var_types_, diag_);
    }
  }

  std::unordered_set<std::string_view> explicit_imported =
      ExplicitlyImportedNames(mod);
  // §26.3 makes every name a wildcard-imported package declares directly
  // visible, and §23.9 makes a generate block a scope whose declarations the
  // module's own symbol table does not list. Both used to skip the whole
  // module, which silenced the check on every other name of it; each is now a
  // set of names the check consults instead.
  std::vector<std::string_view> wildcard_packages =
      WildcardImportedPackages(mod);
  std::unordered_set<std::string_view> generate_names;
  CollectModuleGenerateNames(decl->items, generate_names);
  auto declared = [this, &explicit_imported, &wildcard_packages,
                   &generate_names](std::string_view n) {
    return IsDeclaredNameForRhs(n) || explicit_imported.count(n) != 0 ||
           generate_names.count(n) != 0 ||
           AnyPackageProvidesName(unit_, pkg_provided_names_, wildcard_packages,
                                  n);
  };

  ReportContAssignUnresolved(decl, declared, diag_);
  ReportProcUnresolved(decl, declared, diag_);
  ReportDeclInitUnresolved(decl, declared, diag_);
  ReportSubroutineUnresolved(decl, declared, diag_);

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

}  // namespace delta
