#include "elaborator/elaborator_call_targets.h"

#include <format>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// The calls a module's procedures make by a plain name, each with where it is
// written.
using NamedCalls = std::vector<std::pair<std::string_view, SourceLoc>>;

// Each call by a plain name `expr` holds, itself included, appended to `calls`.
void CollectNamedCalls(const Expr* expr, NamedCalls& calls) {
  if (expr == nullptr) return;
  if (expr->kind == ExprKind::kCall && expr->lhs != nullptr &&
      expr->lhs->kind == ExprKind::kIdentifier) {
    calls.emplace_back(expr->lhs->text, expr->range.start);
  }
  for (const Expr* sub :
       {expr->lhs, expr->rhs, expr->condition, expr->true_expr,
        expr->false_expr, expr->base, expr->index, expr->index_end}) {
    CollectNamedCalls(sub, calls);
  }
  for (const Expr* arg : expr->args) CollectNamedCalls(arg, calls);
  for (const Expr* element : expr->elements) CollectNamedCalls(element, calls);
}

// The bare call statements `stmt` and the statements it holds are, `x;`.
void CollectBareCalls(const Stmt* stmt, NamedCalls& calls) {
  if (stmt == nullptr) return;
  if (stmt->kind == StmtKind::kExprStmt &&
      stmt->expr->kind == ExprKind::kIdentifier) {
    calls.emplace_back(stmt->expr->text, stmt->range.start);
  }
  ForEachChildStmt(stmt,
                   [&](Stmt* const& sub) { CollectBareCalls(sub, calls); });
}

}  // namespace

void ReportCallsOfDataNames(const ModuleDecl& decl, DiagEngine& diag) {
  std::unordered_set<std::string_view> data;
  NamedCalls calls;
  for (const ModuleItem* item : decl.items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      data.insert(item->name);
    }
    if (!IsProceduralItemKind(item->kind)) continue;
    CollectBareCalls(item->body, calls);
    // ForEachStmtReadExpr reaches the statements `body` holds itself.
    ForEachStmtReadExpr(
        item->body, [&](const Expr* expr) { CollectNamedCalls(expr, calls); });
  }
  for (const auto& [name, loc] : calls) {
    if (!data.contains(name)) continue;
    diag.Error(loc,
               std::format("'{}' names a variable or a net, and a call names a "
                           "task or a function",
                           name),
               Subclause("A.8.2"));
  }
}

}  // namespace delta
