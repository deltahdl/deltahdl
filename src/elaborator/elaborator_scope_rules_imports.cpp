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
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

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

// The expressions a case item and a randcase item hold beside their bodies:
// A.6.7 gives a case item its case_item_expressions and §18.16 gives a randcase
// item its weight expression. Neither is a statement, so ForEachChildStmt does
// not reach either and both are read here. The two bodies are left to the
// descent in WalkStmtIdents below, which ForEachChildStmt reaches through
// CaseItem::body and through the second member of a randcase item, so that no
// statement is walked twice.
void WalkStmtCaseIdents(const Stmt* s, std::vector<const Expr*>& out) {
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns) WalkExprIdents(p, out);
  }
  for (const auto& rc : s->randcase_items) WalkExprIdents(rc.first, out);
}

// §26.3 makes a name a wildcard-imported package supplies directly visible to
// a reference written anywhere in the importing scope, so every position a
// statement holds a statement in is a position one of these reads stands in.
// ForEachChildStmt in elaborator_validate_internal.h states those positions
// once for the whole elaborator, which is why the list is not written out again
// here.
void WalkStmtIdents(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  WalkStmtScalarIdents(s, out);
  WalkStmtCaseIdents(s, out);
  ForEachChildStmt(s, [&](Stmt* const& sub) { WalkStmtIdents(sub, out); });
}

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
  // §26.3: the next outer lexical scope a reference this scope does not
  // resolve is searched in, or null for the module's own scope, where the
  // search ends.
  ImportRuleCtx* outer;
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

// §26.3's search for a reference (printed page 810): the current scope's
// locally visible identifiers, then the candidates the wildcard imports
// written before the reference in that scope supply, and, where neither
// matches, the next outer lexical scope the same way, a candidate found there
// imported into that outer scope. The clause's Example 2 (printed 811) has
// `initial x = 1;` in a generate block of a module importing p bind p::x
// through the module's scope, the block's own `import p2::*` standing after
// the reference.
void ProcessImportRuleRef(ImportRuleCtx& ctx, const Expr* e) {
  auto name = e->text;
  if (name.empty()) return;
  for (ImportRuleCtx* scope = &ctx; scope != nullptr; scope = scope->outer) {
    if (scope->seen_decls.count(name)) return;
    if (ClaimWildcardCandidate(*scope, e)) return;
  }
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

void HandleExplicitImport(ImportRuleCtx& ctx, const ModuleItem* item,
                          std::string_view pkg_name) {
  auto name = item->import_item.item_name;
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
  if (!genvar.empty()) seen_decls.insert(genvar);
  ImportRuleCtx ctx{outer.diag,
                    outer.unit,
                    outer.pkg_provided_names,
                    explicit_imports,
                    wildcard_packages,
                    wildcard_claimed,
                    seen_decls,
                    &outer};
  for (const auto* item : items) HandleImportRuleItem(ctx, item);
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
                    seen_decls,
                    nullptr};

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

}  // namespace delta
