// §25.9: the hierarchical references an interface's procedural bodies make to
// objects outside the interface, which bar it from being the type of a virtual
// interface.

#include "elaborator/interface_body_references.h"

#include <string_view>
#include <unordered_set>

#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using Names = std::unordered_set<std::string_view>;

// Adds the names the statement `s` and the statements under it declare: a
// block's variables, a foreach loop's index variables, and a block's label.
void CollectBodyNames(const Stmt* s, Names& names) {
  if (s == nullptr) return;
  names.insert(s->var_name);
  names.insert(s->label);
  names.insert(s->foreach_vars.begin(), s->foreach_vars.end());
  ForEachChildStmt(s, [&](Stmt* const& sub) { CollectBodyNames(sub, names); });
}

// The first name of the dotted name `e`, `top` of `top.u[0].x`; empty where
// `::` stands along it, or where it starts with no name.
std::string_view DottedRoot(const Expr* e) {
  while (e->kind == ExprKind::kMemberAccess || e->kind == ExprKind::kSelect) {
    if (e->is_scope_resolution) return {};
    e = e->kind == ExprKind::kSelect ? e->base : e->lhs;
  }
  bool named = e->kind == ExprKind::kIdentifier && e->scope_prefix.empty();
  return named ? e->text : std::string_view{};
}

bool ExprRefersOutside(const Expr* e, const Names& names) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kMemberAccess && !names.contains(DottedRoot(e))) {
    return true;
  }
  return AnyExprChild(
      e, [&](const Expr* child) { return ExprRefersOutside(child, names); });
}

bool StmtRefersOutside(const Stmt* s, const Names& names) {
  if (s == nullptr) return false;
  for (const Expr* e : {s->lhs, s->rhs, s->expr, s->condition, s->var_init}) {
    if (ExprRefersOutside(e, names)) return true;
  }
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    found = found || StmtRefersOutside(sub, names);
  });
  return found;
}

// The statements of `item`'s body: a process's one, or a task's or a
// function's list.
bool ItemBodyRefersOutside(const ModuleItem* item, const Names& local) {
  Names names = local;
  // The name an empty DottedRoot answers with, which is no reference.
  names.insert(std::string_view{});
  for (const FunctionArg& arg : item->func_args) names.insert(arg.name);
  CollectBodyNames(item->body, names);
  for (const Stmt* s : item->func_body_stmts) CollectBodyNames(s, names);
  if (StmtRefersOutside(item->body, names)) return true;
  for (const Stmt* s : item->func_body_stmts) {
    if (StmtRefersOutside(s, names)) return true;
  }
  return false;
}

}  // namespace

bool BodyRefersOutsideInterface(const ModuleDecl* iface, const Names& local) {
  for (const ModuleItem* item : iface->items) {
    if (item->body == nullptr && item->func_body_stmts.empty()) continue;
    if (ItemBodyRefersOutside(item, local)) return true;
  }
  return false;
}

}  // namespace delta
