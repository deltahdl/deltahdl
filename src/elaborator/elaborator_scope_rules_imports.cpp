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

// The identifiers a reference reads, a dotted name (§23.7) by its first name.
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

// The expressions a case item and a randcase item hold beside their bodies:
// A.6.7 gives a case item its case_item_expressions and §18.16 gives a randcase
// item its weight expression. Neither is a statement, so ForEachChildStmt does
// not reach either and both are read here. The two bodies are left to the
// descent in WalkStmtIdents below, which ForEachChildStmt reaches through
// CaseItem::body and through the second member of a randcase item, so that no
// statement is walked twice.
void WalkStmtCaseIdents(const Stmt* s, std::vector<Expr*>& out) {
  for (const auto& ci : s->case_items) {
    for (auto* p : ci.patterns) WalkExprIdents(p, out);
  }
  for (const auto& rc : s->randcase_items) WalkExprIdents(rc.first, out);
}

// §26.3 makes a name a wildcard-imported package supplies directly visible to
// a reference written anywhere in the importing scope, so every position a
// statement holds a statement in is a position one of these reads stands in.
// ForEachChildStmt in elaborator_validate_internal.h states those positions
// once for the whole elaborator, which is why the list is not written out again
// here.
void WalkStmtIdents(const Stmt* s, std::vector<Expr*>& out) {
  if (!s) return;
  WalkStmtScalarIdents(s, out);
  WalkStmtCaseIdents(s, out);
  ForEachChildStmt(s, [&](Stmt* const& sub) { WalkStmtIdents(sub, out); });
}

using OuterBoundRefs =
    std::unordered_map<std::string_view,
                       std::vector<std::pair<Expr*, std::string_view>>>;

// §26.3 (printed page 810): what settling a module-level reference that no
// import written before it resolved takes: the packages the module's body
// imports by wildcard anywhere, and whether the module declares the name,
// whether the compilation unit declares it as data before the module, and
// whether anything else the module reaches declares it.
struct LateImportCheck {
  const std::vector<std::string_view>& wildcards;
  std::function<bool(std::string_view)> module_declares;
  std::function<bool(std::string_view)> unit_data;
  std::function<bool(std::string_view)> declared;
};

// Mutable state shared across the import-rule checking helpers below: one
// scope's locally visible identifiers, its explicit imports and the packages
// its wildcard imports name, with the names those have been made to supply.
// Holds references to the Elaborator members for the module's scope and to
// per-call locals for a generate block's, so the phases can be expressed as
// free functions.
struct ImportRuleCtx {
  DiagEngine& diag;
  const CompilationUnit* unit;
  ProvidedNameCache& pkg_provided_names;
  std::unordered_map<std::string_view, std::pair<std::string_view, SourceLoc>>&
      explicit_imports;
  std::vector<std::string_view>& wildcard_packages;
  std::unordered_map<std::string_view, SourceLoc>& wildcard_claimed;
  std::unordered_set<std::string_view>& seen_decls;
  // §23.7 with §26.3: the references standing in this scope, or in one inside
  // it, that an outer scope's wildcard import bound, by the name each reads,
  // with the package declaring what it bound.
  OuterBoundRefs& outer_bound;
  // §26.3: the next outer lexical scope a reference this scope does not
  // resolve is searched in, or null for the module's own scope, where the
  // search ends.
  ImportRuleCtx* outer;
  // The module's own scope's LateImportCheck; null for a generate block's.
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
  // §23.7 with §26.3: a reference an outer scope's wildcard import bound
  // stays bound to the package's declaration when this scope declares the
  // name after it, so it is read through that package.
  auto bound = ctx.outer_bound.find(name);
  if (bound == ctx.outer_bound.end()) return;
  for (auto& [ref, origin] : bound->second) ref->scope_prefix = origin;
  ctx.outer_bound.erase(bound);
}

// §26.3 makes it illegal for the wildcard imports of more than one package to
// define the same potentially locally visible identifier that a reference
// matches (printed page 810), and §26.6 makes an import of a declaration
// reached through an export an import of the original declaration, so that
// reaching one declaration by several exported paths is no conflict (printed
// 815): the clause's own `import p2::*; import p4::*; int y = x;` reads p1's x
// through both. The wildcard-imported packages supplying `name` are therefore
// counted by the package declaring it, a second supplier of the same
// declaration adding nothing. Answers whether the scope's wildcard imports
// settled the reference, by a claim or by the conflict.
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

// The declaration an explicit import of `pkg_name::name` imports, named by
// the package declaring it: §26.6 makes an import of a declaration reached
// through an export an import of the original declaration (printed page 815),
// so the origin is the source's own declaration or the one an export of the
// source hands on. The source itself stands in where it provides no such
// name, the import of a name its package lacks being the import's own report.
std::string_view ExplicitImportOrigin(ImportRuleCtx& ctx,
                                      std::string_view pkg_name,
                                      std::string_view name) {
  std::string_view origin =
      ProvidedNameOrigin(ctx.unit, ctx.pkg_provided_names, pkg_name, name);
  return origin.empty() ? pkg_name : origin;
}

// The package declaring the identifier a reference bound through the scope's
// wildcard imports. ClaimWildcardCandidate claims a name only where one
// declaration supplies it, so the first supplier's origin is the claim's.
std::string_view WildcardClaimOrigin(ImportRuleCtx& ctx,
                                     std::string_view name) {
  for (auto pkg : ctx.wildcard_packages) {
    std::string_view origin =
        ProvidedNameOrigin(ctx.unit, ctx.pkg_provided_names, pkg, name);
    if (!origin.empty()) return origin;
  }
  return {};
}

// The first of the wildcard-imported packages `packages` that provides
// `name`; empty where none does.
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

// §23.7 (printed pages 757-758) with §26.3: a reference `binder`'s wildcard
// import bound from the scope `from` inside it is noted on every scope from
// `from` out to `binder`, any of which may declare the name after the
// reference. The clause's dotted name 2 has `s2.x` in a generate block bind
// the structure p::s2 the module imports, the instance s2 the block declares
// after it not yet being visible.
void NoteOuterBinding(ImportRuleCtx& from, ImportRuleCtx& binder, Expr* e) {
  std::string_view origin = WildcardClaimOrigin(binder, e->text);
  for (ImportRuleCtx* scope = &from; scope != &binder; scope = scope->outer) {
    scope->outer_bound[e->text].push_back({e, origin});
  }
}

// §26.3's search for a reference (printed page 810): the current scope's
// locally visible identifiers, then the candidates the wildcard imports
// written before the reference in that scope supply, and, where neither
// matches, the next outer lexical scope the same way, a candidate found there
// imported into that outer scope. The clause's Example 2 (printed 811) has
// `initial x = 1;` in a generate block of a module importing p bind p::x
// through the module's scope, the block's own `import p2::*` standing after
// the reference.
// §26.3 (printed page 810): a module-level reference no scope resolved, where
// a wildcard import written after it in the module would supply the name. The
// import does not reach back to it, so the search ends in the compilation
// unit: the reference reads the unit's data of the name, recorded on it as
// `$unit::` records it (§3.12.1), and with no declaration of the name to reach
// it is reported. A name the module, or anything else it reaches, declares is
// left to the checks of its own.
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

// §26.3 makes an explicit import illegal where the identifier is explicitly
// imported from another package, an import of the same identifier from the
// same package allowed (printed page 810), and §26.6 makes importing one
// declaration by several exported paths no conflict (printed 815-816): the
// clause's p2 and p4 both hand on p1's x, so `import p2::x; import p4::x;`
// imports one declaration twice. The two imports are therefore compared by
// the declaration each reaches rather than by the package each names.
// Answers whether an earlier explicit import settled this one.
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

// Table 26-1 of §26.5, row `import p::c;`, column for a scope holding a
// wildcard import of c (printed page 814): the explicit import makes every
// earlier reference to c illegal. §26.3 states the other three import-legality
// rules this file enforces but not this one, and the worked example closing
// §26.5 (`import q::*; wire a = c; import p::c;`) is this rule alone. The
// reference bound the wildcard-imported declaration, and the explicit import
// would bind the name to another; where it names that same declaration,
// reached through an export, §26.6 has the two imports agree (printed 816)
// and nothing is rebound. Answers whether the explicit import was reported.
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

// §26.3 (printed page 809) with §26.6 (printed 815): an explicit import
// imports the declaration the package makes visible under the name, its own
// or one an export hands on, and std's are Annex G's (§26.7); a name the
// package neither declares nor exports is no candidate for import, what it
// imports without exporting included. Answers whether the import was reported.
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

// §26.3 (printed page 808): the compilation of a package precedes that of the
// scopes importing it, so an import written ahead of the package it names has
// no package yet to import from. Answers whether the import was reported.
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

// §27.5 and §27.4 make a generate block a scope of its own, nested in the
// scope its construct is written in, and §26.3 has an import written among
// the block's items make its names candidates for the block's references
// after it alone: a reference in the block is searched in the block first,
// its declarations and then those candidates, and only then outward. The
// block's scope starts empty rather than pre-seeded as the module's is, so a
// reference before the block's own import is the enclosing scope's to
// resolve, as Example 2 has it. §27.4's loop generate block declares the
// genvar as an implicit localparam of every block instance, so `genvar` is
// among the block's own names.
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

// §26.3 (printed pages 809-810) with A.2.8: a task or function body is a scope
// of its own, its formals, its result and its declarations its locally visible
// names, and an import among its block item declarations makes names
// candidates for the body's references after it alone. The body is walked as
// a scope nested in the one the subroutine stands in, in source order: a local
// variable is a declaration once its initializer has been read, and a let, a
// typedef or an import is the item it carries.
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

// The genvar a loop generate construct is written over (§27.4), whether
// declared in the loop's own initialization or before it, or empty for a
// conditional construct.
std::string_view GenerateLoopVariable(const ModuleItem* item) {
  const Stmt* init = item->gen_init;
  if (init == nullptr) return {};
  if (!init->var_name.empty()) return init->var_name;
  if (init->lhs != nullptr && init->lhs->kind == ExprKind::kIdentifier) {
    return init->lhs->text;
  }
  return {};
}

// Walks every generate block of the construct as a scope nested in `ctx`. An
// else branch is itself a conditional construct (Parser::ParseGenerateIf
// makes a plain else one with no condition), so it is handled as one item; a
// case construct holds its blocks in its items. Every alternative is walked,
// the check running before the construct's condition is evaluated, and each is
// a scope of its own so none reaches another's declarations.
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
      // §8.24: an out-of-block method body reads its class's members, which
      // no scope here holds, and is the class's to check.
      if (item->method_class.empty()) {
        HandleSubroutineImportRules(ctx, item);
      } else {
        TrackImportRuleDecl(ctx, item->name, item->loc);
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
      // package's enum members are treated as wildcard-import candidates, and
      // from an enumeration written as the type of a structure or union member
      // of either (§7.2), which §23.9 makes no scope of its own.
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

  // §26.3 (printed page 810): a wildcard import makes its names candidates for
  // the references after it alone, so the scope's packages are gathered as the
  // walk below reaches each import; every one the body writes is kept apart
  // for a reference written ahead of the import that supplies it.
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
