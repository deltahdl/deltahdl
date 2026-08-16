#include "elaborator/elaborator_scope_rules_names.h"

#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

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

}  // namespace

// The operands of `e` that a value read could name. Three kinds of node hold an
// identifier-shaped child that names something other than a value, and each is
// left out:
//
//   - the callee of a call, which Parser::ParseCallExpr writes into lhs. §23.9
//     rules that the search for "a task, function, named block, or generate
//     block ... continues to search higher level modules until found", so a
//     callee is not held to the module boundary a variable read is held to.
//   - the slice size or type of a §11.4.14.2 streaming concatenation, which
//     Parser::ParseStreamingConcat writes into lhs. `{<< 8 {a}}` puts the 8
//     there as an identifier node, and it names a width rather than a value.
//   - the member name of a §7.3.2 tagged union expression, which
//     Parser::ParseTaggedExpr writes into rhs. `tagged Valid x` names a member
//     of the union type there, not a declaration of the enclosing scope.
//
// Expr::with_expr is left out whatever the node is. §7.12.1 binds the iterator
// name an array method's `with` clause reads -- `q.sum() with (item)` declares
// `item` at the call -- and §18.7 resolves the names of an inline constraint
// block against the object being randomized, so neither is a name the enclosing
// module declares.
static void CollectBareIdentOperands(const Expr* e,
                                     std::vector<const Expr*>& out) {
  bool lhs_names_no_value =
      e->kind == ExprKind::kCall || e->kind == ExprKind::kStreamingConcat;
  if (!lhs_names_no_value) CollectBareIdents(e->lhs, out);
  if (e->kind != ExprKind::kTagged) CollectBareIdents(e->rhs, out);
  CollectBareIdents(e->base, out);
  CollectBareIdents(e->index, out);
  CollectBareIdents(e->index_end, out);
  CollectBareIdents(e->condition, out);
  CollectBareIdents(e->true_expr, out);
  CollectBareIdents(e->false_expr, out);
  CollectBareIdents(e->repeat_count, out);
  for (const auto* a : e->args) CollectBareIdents(a, out);
  for (const auto* el : e->elements) CollectBareIdents(el, out);
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
    // `null` (§6.24.1) and the `$` of an open range or a queue's last index
    // (§7.10.1) parse as identifier-shaped nodes and name no declaration, so
    // neither is a read this can find a declaration for.
    if (e->scope_prefix.empty() && !IsBuiltinTypeKeyword(e->text) &&
        e->text != "null" && e->text != "$") {
      out.push_back(e);
    }
    return;
  }
  CollectBareIdentOperands(e, out);
}

// The packages a module imports by wildcard. §26.3 makes every name such a
// package declares directly visible, so a bare read of one resolves, and the
// module's own symbol table does not enumerate them. Each name is looked up in
// these packages rather than the module skipped whole, because skipping
// silences the check on every other name of the module too.
std::vector<std::string_view> WildcardImportedPackages(const RtlirModule* mod) {
  std::vector<std::string_view> pkgs;
  for (const auto& imp : mod->imports) {
    if (imp.is_wildcard) pkgs.push_back(imp.package_name);
  }
  return pkgs;
}

static void CollectGenerateBodyNames(
    const std::vector<ModuleItem*>& items,
    std::unordered_set<std::string_view>& names);

// The names one generate construct declares: the label of each of its blocks,
// the loop variable §27.4 makes an implicit localparam of each generated block,
// and the name of every item declared inside one.
static void CollectOneGenerateNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& names) {
  const Stmt* init = item->gen_init;
  if (init != nullptr && init->lhs != nullptr &&
      init->lhs->kind == ExprKind::kIdentifier) {
    names.insert(init->lhs->text);
  }
  if (init != nullptr && !init->var_name.empty()) names.insert(init->var_name);
  CollectGenerateBodyNames(item->gen_body, names);
  if (item->gen_else != nullptr) {
    CollectGenerateBodyNames(item->gen_else->gen_body, names);
  }
  for (const auto& ci : item->gen_case_items) {
    CollectGenerateBodyNames(ci.body, names);
  }
}

// Over-approximated set of the names a module's generate constructs declare,
// and of its genvars. §23.9 makes a generate block a scope of its own, so the
// elaborated module's symbol table does not list what one declares, and a flat
// set holds names that are declared per block rather than module-wide.
// Over-approximating is safe for the reason CollectProcLocalNames records: a
// name in the set can only suppress a diagnostic, never raise one.
static void CollectGenerateBodyNames(
    const std::vector<ModuleItem*>& items,
    std::unordered_set<std::string_view>& names) {
  for (const auto* item : items) {
    if (!item->name.empty()) names.insert(item->name);
    if (item->kind == ModuleItemKind::kGenerateFor ||
        item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase) {
      CollectOneGenerateNames(item, names);
    }
  }
}

// The same over a module's own items, where only a genvar and what a generate
// construct declares are names the module's symbol table does not already list.
void CollectModuleGenerateNames(const std::vector<ModuleItem*>& items,
                                std::unordered_set<std::string_view>& names) {
  for (const auto* item : items) {
    if (item->is_genvar && !item->name.empty()) names.insert(item->name);
    if (item->kind == ModuleItemKind::kGenerateFor ||
        item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase) {
      CollectOneGenerateNames(item, names);
    }
  }
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

// Collects the bare identifier reads of every procedural blocking/nonblocking
// assignment's right side, dropping the ones a block-local declaration names.
// The caller then rejects any that resolve to no declaration.
//
// CollectBareIdents is what walks each right side, so a read written inside a
// larger expression is reached under the same guards a continuous assignment's
// whole right side is already walked under: no descent into a member access, so
// the base of `a.b`, `pkg::x` and a `with` clause hanging off one is never
// collected, and no scope-prefixed name, builtin type keyword, `null` or `$`.
// Those guards are what keep this free of false positives; an earlier version
// took the right side only when the whole of it was one identifier, which left
// `r = v + 0;` unchecked.
void CollectProcRhsIdents(const Stmt* s,
                          const std::unordered_set<std::string_view>& locals,
                          std::vector<const Expr*>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    std::vector<const Expr*> refs;
    CollectBareIdents(s->rhs, refs);
    for (const auto* r : refs) {
      if (locals.count(r->text) == 0) out.push_back(r);
    }
  }
  for (const auto* sub : s->stmts) CollectProcRhsIdents(sub, locals, out);
  for (const auto* sub : s->fork_stmts) CollectProcRhsIdents(sub, locals, out);
  CollectProcRhsIdents(s->then_branch, locals, out);
  CollectProcRhsIdents(s->else_branch, locals, out);
  CollectProcRhsIdents(s->body, locals, out);
  CollectProcRhsIdents(s->for_body, locals, out);
  for (const auto* fi : s->for_inits) CollectProcRhsIdents(fi, locals, out);
  for (const auto* fs : s->for_steps) CollectProcRhsIdents(fs, locals, out);
  for (const auto& ci : s->case_items)
    CollectProcRhsIdents(ci.body, locals, out);
}

// The names a subroutine's body may read without the module declaring them:
// §13.3 makes each formal argument a declaration of the subroutine, §13.4.1
// makes a function's own name a variable of it, and a body may declare its own.
void CollectSubroutineLocalNames(const ModuleItem* item,
                                 std::unordered_set<std::string_view>& names) {
  if (!item->name.empty()) names.insert(item->name);
  for (const auto& arg : item->func_args) {
    if (!arg.name.empty()) names.insert(arg.name);
  }
  for (const auto* stmt : item->func_body_stmts) {
    if (stmt != nullptr && stmt->kind == StmtKind::kBlockItemDecl &&
        stmt->decl_item != nullptr && !stmt->decl_item->name.empty()) {
      names.insert(stmt->decl_item->name);
    }
    CollectProcLocalNames(stmt, names);
  }
}

}  // namespace delta
