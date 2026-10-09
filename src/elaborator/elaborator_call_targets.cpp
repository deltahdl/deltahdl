#include "elaborator/elaborator_call_targets.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// The names a walk of one module's procedures sees as variables or nets: the
// module's own, and those each block around the statement walked declares,
// the innermost last (§23.9).
struct DataScope {
  std::unordered_set<std::string_view> module;
  std::vector<std::string_view> blocks;

  bool Names(std::string_view name) const {
    return module.contains(name) ||
           std::ranges::find(blocks, name) != blocks.end();
  }
};

// Reports a call of `name` written at `loc` where the scope sees the name as
// a variable or a net.
void ReportIfData(std::string_view name, SourceLoc loc, const DataScope& scope,
                  DiagEngine& diag) {
  if (!scope.Names(name)) return;
  diag.Error(loc,
             std::format("'{}' names a variable or a net, and a call names a "
                         "task or a function",
                         name),
             Subclause("A.8.2"));
}

// Each call by a plain name `expr` holds, itself included. A constructor call
// is no call by a name: its `lhs` is the object a shallow copy copies,
// `new src` (§8.12).
void CheckExprCalls(const Expr* expr, const DataScope& scope,
                    DiagEngine& diag) {
  if (expr == nullptr) return;
  if (expr->kind == ExprKind::kCall && expr->lhs != nullptr &&
      expr->text != "new" && expr->lhs->kind == ExprKind::kIdentifier) {
    ReportIfData(expr->lhs->text, expr->range.start, scope, diag);
  }
  ForEachExprChild(
      expr, [&](const Expr* child) { CheckExprCalls(child, scope, diag); });
}

// The calls `stmt` and the statements it holds make by a plain name: a bare
// call statement, `x;`, and each call an expression of theirs holds, with the
// variables a block declares in scope over the statements the block holds.
void CheckStmtCalls(const Stmt* stmt, DataScope& scope, DiagEngine& diag) {
  if (stmt == nullptr) return;
  const std::size_t kOuter = scope.blocks.size();
  if (stmt->kind == StmtKind::kBlock || stmt->kind == StmtKind::kFork) {
    const std::vector<Stmt*>& items =
        stmt->kind == StmtKind::kFork ? stmt->fork_stmts : stmt->stmts;
    for (const Stmt* item : items) {
      if (item->kind == StmtKind::kVarDecl)
        scope.blocks.push_back(item->var_name);
    }
  }
  if (stmt->kind == StmtKind::kExprStmt &&
      stmt->expr->kind == ExprKind::kIdentifier) {
    ReportIfData(stmt->expr->text, stmt->range.start, scope, diag);
  }
  ForEachChildExpr(
      stmt, [&](const Expr* expr) { CheckExprCalls(expr, scope, diag); });
  ForEachChildStmt(stmt,
                   [&](Stmt* const& sub) { CheckStmtCalls(sub, scope, diag); });
  scope.blocks.resize(kOuter);
}

}  // namespace

void ReportCallsOfDataNames(const ModuleDecl& decl, DiagEngine& diag) {
  DataScope scope;
  for (const ModuleItem* item : decl.items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      scope.module.insert(item->name);
    }
  }
  for (const ModuleItem* item : decl.items) {
    if (IsProceduralItemKind(item->kind))
      CheckStmtCalls(item->body, scope, diag);
  }
}

}  // namespace delta
