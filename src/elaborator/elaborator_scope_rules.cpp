#include <algorithm>
#include <cstddef>
#include <format>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// A.6.9 makes a bare identifier standing as a statement a
// subroutine_call_statement, the enabling of a task of that name (§13.3), so
// the name is a reference §23.9 resolves like any other. `delay_number` is
// the text of the number a delay control written immediately before it takes
// as its delay, `2.1` for `#2.1 ns;`, and empty for every other position:
// §5.8 (printed page 80) has a time literal be its number followed without a
// space by its unit, so a unit name standing there as a call is the one
// mistake the report can name.
struct BareCall {
  std::string_view name;
  SourceLoc loc;
  std::string_view delay_number;
};

struct ScopeWalk {
  std::vector<std::pair<std::string_view, SourceLoc>> block_labels;
  std::unordered_set<std::string_view> local_names;
  std::vector<std::pair<std::string_view, SourceLoc>> proc_lhs;
  std::vector<BareCall> bare_calls;
  // The statement each numeric delay control holds, keyed to the number's
  // text, for CollectBareCall to read when the walk reaches the statement.
  std::unordered_map<const Stmt*, std::string_view> delayed_bodies;
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

// The bare identifier `s` is when it is a statement of that shape, or null.
const Expr* BareCallOf(const Stmt* s) {
  if (s == nullptr || s->kind != StmtKind::kExprStmt || s->expr == nullptr ||
      s->expr->kind != ExprKind::kIdentifier)
    return nullptr;
  return s->expr;
}

// Records the bare call `s` is, with the number of the delay control whose
// statement it is when there is one. A delay control is walked before its
// statement, so the statement a numeric delay holds is noted here and found
// when the walk reaches it.
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
  CollectBareCall(s, out);
  // §23.9 makes a block label, a local declaration and an assignment target
  // part of the scope they are written in wherever the statement holding them
  // stands, so every position a statement holds a statement in is one this
  // collection reaches. ForEachChildStmt in elaborator_validate_internal.h
  // states those positions once for the whole elaborator, which is why the
  // list is not written out again here. The visitor takes `Stmt* const&`
  // because `s` is a `const Stmt*`, which is how ForEachChildStmt lets a walk
  // that only reads the tree share its list with the walks that rewrite it.
  //
  // §12.7.1: the control variables a for-loop header declares are in scope
  // while the loop's own sub-statements are walked and are dropped afterwards
  // so they do not leak outward. The push brackets the whole descent rather
  // than Stmt::for_inits, Stmt::for_steps and Stmt::for_body alone, because
  // PushTypedForInitVars pushes nothing unless Stmt::for_inits holds
  // something, which A.6.8 admits on a for-loop statement alone, and a
  // for-loop statement holds its sub-statements in those three members and no
  // other.
  size_t pushed = PushTypedForInitVars(s, out);
  ForEachChildStmt(s, [&](Stmt* const& sub) { CollectScopeWalk(sub, out); });
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
  // §23.9 puts no condition on where the block whose declarations it governs
  // is written, so every position a statement holds a statement in is a
  // position a begin-end or fork-join block stands in. ForEachChildStmt in
  // elaborator_validate_internal.h states those positions once for the whole
  // elaborator, which is why the list is not written out again here.
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckBlockLocalRedeclarations(sub, diag); });
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
  // §8.30.1 puts no condition on where the declaration it governs is written,
  // so every position a statement holds a statement in is a position a
  // weak_reference variable is declared in. ForEachChildStmt in
  // elaborator_validate_internal.h states those positions once for the whole
  // elaborator, which is why the list is not written out again here.
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

// The package declaring `name` as the wildcard-imported package `pkg_name`
// provides it, or empty where `pkg_name` does not provide the name.
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

// §26.3 with §23.9: a package variable an import of `items` makes visible --
// an explicit import naming it, or a wildcard import of a package declaring
// it -- is a target of a procedural assignment as the module's own
// declaration is, so a write to it names nothing undeclared. The names come
// from the import items themselves, since this check runs without the
// RtlirModule the read-side check takes its imports from.
static bool ImportsProvideName(const CompilationUnit* unit,
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

// §3.12.1 with §13.3: a task or function declared at compilation-unit scope
// is what a bare call in a module of the unit reaches when the module declares
// none of the name, as a unit's data declaration is for an assignment target.
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

// Syntax 5-2: the six time_unit spellings.
static bool IsTimeUnitName(std::string_view name) {
  return name == "s" || name == "ms" || name == "us" || name == "ns" ||
         name == "ps" || name == "fs";
}

// Reports each bare call that `visible` answers false for: a unit name that
// stands as the statement of a numeric delay under §5.8, since `#2.1 ns;` is
// the time literal `2.1ns` written with a space and nothing else the
// standard admits, and any other name as §23.9's unresolved reference.
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
  // §3.12.1 (printed page 56) has an import written at compilation-unit
  // scope stand for the module too, as the read-side check honours it, and
  // the unit's own variable and net declarations likewise, which §6.21
  // (printed 132) gives a static lifetime: `int g;` outside every module
  // with `initial g = 5;` in a module was reported as undeclared, while a
  // unit function's or class's name still is (UnitDeclaresData in
  // elaborator_items.cpp asks the unit's items for a data declaration).
  auto target_visible = [&](std::string_view name) {
    return walk.local_names.count(name) != 0 || IsNameInModuleScope(name) ||
           ImportsProvideName(unit_, pkg_provided_names_, decl->items, name) ||
           ImportsProvideName(unit_, pkg_provided_names_, unit_->cu_items,
                              name) ||
           UnitDeclaresData(unit_, name);
  };
  for (const auto& [name, loc] : walk.proc_lhs) {
    if (target_visible(name)) continue;
    diag_.Error(loc, std::format("undeclared identifier '{}'", name),
                Subclause("23.9"));
  }
  // A bare call reaches every name an assignment target does, and the unit's
  // tasks and functions besides, which no assignment target may name.
  ReportBareCallsNamingNothing(
      walk,
      [&](std::string_view name) {
        return target_visible(name) || UnitDeclaresSubroutine(unit_, name);
      },
      diag_);
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
  // §6.16 makes a string and a numeric type incompatible whatever statement
  // the assignment between them stands in, so every position a statement holds
  // a statement in is a position the report is made at. ForEachChildStmt in
  // elaborator_validate_internal.h states those positions once for the whole
  // elaborator, which is why the list is not written out again here.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckStringNumericAssigns(sub, var_types, diag);
  });
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

// The package import declarations a subroutine body opens with. A.2.8 admits
// package_import_declaration as a block_item_declaration, which A.2.7's
// tf_item_declaration takes, and the parser keeps each as a kBlockItemDecl
// statement holding the import item (Parser::ParseBlockVarDecls).
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

// §23.9: rejects an unresolved bare identifier read in a task or function body.
// §23.9 lists a task and a function among the scopes an identifier is searched
// upward from, and rules that the search "shall stop at a module boundary" when
// the item is a variable, so a subroutine body is held to the boundary exactly
// as a procedural block of the same module is. An out-of-block method body
// (§8.24), the item whose `method_class` names its class, is not held to it:
// §8.24 has the body read every declaration of its class, the properties it
// inherits under §8.13 included, none of which the module declares, so it is
// left to the class rules as a body of the compilation unit's class is.
//
// §26.3 makes an import declaration provide its names "within the current
// scope", and the body is a scope of its own, so an import the body opens
// with (SubroutineBodyImports) is honoured for the body's reads alone: `K` in
// `function int calc(); import p::*; return K * five(); endfunction` is p's
// parameter, which the module the function stands in never imported.
//
// Written over an item list rather than over a module because a subroutine the
// compilation unit or a package holds is in no module's list (see
// ReportUnresolvedInUnitScopeSubroutines below); a module passes its own.
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
    ReportUnresolvedRefs(refs, declared_in_body, diag);
  }
}

// Collects every scope-resolution member access (`base::member`, marked
// is_scope_resolution by the parser) whose base is a plain identifier,
// recursing through the whole expression tree so nested forms (`a::b::c`,
// scope refs inside calls/concats) are reached. System scopes (`$unit::`,
// `$root.`) carry their prefix in scope_prefix and are skipped here.
void CollectScopeBases(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->is_scope_resolution && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier && e->lhs->scope_prefix.empty() &&
      !e->lhs->text.starts_with("$")) {
    out.push_back(e);
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
  // §26.3 puts no condition on where the assignment carrying a scope-resolution
  // prefix stands, so every position a statement holds a statement in is one
  // this collection reaches. ForEachChildStmt in
  // elaborator_validate_internal.h states those positions once for the whole
  // elaborator, which is why the list is not written out again here.
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CollectProcScopeBases(sub, out); });
}

// §26.3 (printed page 808) references a declaration made in a package through
// the package scope resolution operator, and §26.6 (printed 815) has a
// declaration the package imported reachable through the package only where
// an export hands it on, `import p1::x; export p1::x;` making p1::x and p2::x
// one declaration. `provided` answers whether the base package makes the
// member available so, by its own declaration or by an exported one; a scoped
// reference to a name the package imports without exporting, or never sees,
// is reported.
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

// §26.3: a scope-resolution prefix `base::` shall name a package (or a class /
// type, for static-member and type-scope access). `known` accepts those base
// names; "std" is the always-available built-in package. Any other base is an
// unresolved package or scope. A base that is known is then asked for the
// member, which `provided` answers for a package of the unit and accepts for
// every other base.
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
    if (b->text == "std" || b->text == "local") continue;
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
static bool AnyPackageProvidesName(const CompilationUnit* unit,
                                   ProvidedNameCache& provided_cache,
                                   const std::vector<std::string_view>& pkgs,
                                   std::string_view name) {
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
  ReportSubroutineUnresolved(decl->items, declared, unit_, pkg_provided_names_,
                             diag_);

  // §26.3: a `pkg::x` scope prefix must name a known package (or a class/type
  // for static-member / type-scope access). cu_scope_names_ holds packages,
  // classes, and interfaces; class_names_ and typedefs_ cover module-local
  // classes and type names; and a class a package declares is visible by its
  // bare name where an import, wildcard or explicit, has brought it in, so it
  // stands as a base too -- `c = pk_t::get();` after `import p::*` was reported
  // while `p::pk_t::get()` was not.
  //
  // §26.6: the member of a `pkg::x` written on a package the unit declares is
  // one the package declares or exports; a class or typedef of the module
  // standing under a package's name is the base §8.23 takes first, and a base
  // that is no package of the unit -- a class, an interface, an imported class
  // -- has its members checked elsewhere. A `name[N]` enumeration member of
  // §6.19.2 stands in the provided names under the constants it generates,
  // name0 through nameN-1, and not under the written name (Table 6-10,
  // printed page 121), so `pkg::name` is reported while `pkg::name1` is
  // provided; the constants are also read under their "pkg.name1" keys
  // (RegisterPackageParams in elaborator_resolve.cpp), which is what answers
  // for a member whose bound the provided-name walk could not fold.
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
      [this, &explicit_imported, &wildcard_packages](std::string_view n) {
        return IsKnownScopeBase(n, cu_scope_names_, class_names_, typedefs_,
                                unit_) ||
               explicit_imported.count(n) != 0 ||
               AnyPackageProvidesName(unit_, pkg_provided_names_,
                                      wildcard_packages, n);
      },
      provided, diag_);
}

// §23.9 over the subroutines no module holds. Every walk above runs from
// Elaborator::ValidateUnresolvedReferences, once per elaborated module and over
// that module's items, and §3.12.1 puts a subroutine outside every design
// element in the compilation-unit scope while Clause 26 puts one in a package;
// neither is in any module's list, so a read in either body was never
// resolved, and `function int f(); return undeclared; endfunction` at the top
// of a file elaborated clean. This is the walk over those two scopes, run
// from Elaborator::ValidatePerDeclarationRulesInUnitScopes beside the other
// per-declaration rules that scope keeps.
//
// What a compilation-unit body can reach is what RegisterCuScopeItems recorded
// of the unit's items, held in `names`: the item names, the constants (§6.19's
// enumeration members and §6.20.4's local parameters, by bare name), the
// typedefs and the classes; and the names the unit's own import declarations
// provide (§26.3, ImportsProvideName over the unit's items). A package body
// reaches its own items, the members of the enumerations its items declare
// (§6.19 -- RegisterPackageParams records those in the constants map under the
// qualified `pkg.NAME` alone, so they are read off the items here through
// ForEachEnumTypeOfItem) and its own imports, on top of the unit's. The body's
// formals, locals and body-level imports are the walk's own business, as they
// are for a module's subroutine.
void ReportUnresolvedInUnitScopeSubroutines(const CompilationUnit* unit,
                                            const UnitScopeNames& names,
                                            ProvidedNameCache& provided_cache,
                                            DiagEngine& diag) {
  auto unit_declares = [&](std::string_view n) {
    return names.item_names.count(n) != 0 || names.constants.count(n) != 0 ||
           names.typedefs.count(n) != 0 || names.class_names.count(n) != 0 ||
           ImportsProvideName(unit, provided_cache, unit->cu_items, n);
  };
  ReportSubroutineUnresolved(unit->cu_items, unit_declares, unit,
                             provided_cache, diag);
  for (const auto* pkg : unit->packages) {
    if (pkg == nullptr) continue;
    std::unordered_set<std::string> pkg_names;
    for (const auto* item : pkg->items) {
      if (item == nullptr) continue;
      if (!item->name.empty()) pkg_names.insert(std::string(item->name));
      ForEachEnumTypeOfItem(
          item, [&](std::string_view, const DataType& enum_type) {
            for (const auto& member : enum_type.enum_members) {
              for (auto& n : EnumMemberDeclaredNames(member, names.constants))
                pkg_names.insert(std::move(n));
            }
          });
    }
    auto pkg_declares = [&](std::string_view n) {
      return pkg_names.count(std::string(n)) != 0 || unit_declares(n) ||
             ImportsProvideName(unit, provided_cache, pkg->items, n);
    };
    ReportSubroutineUnresolved(pkg->items, pkg_declares, unit, provided_cache,
                               diag);
  }
}

}  // namespace delta
