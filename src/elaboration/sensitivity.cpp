#include "elaboration/sensitivity.h"

#include "common/arena.h"
#include "parser/ast.h"

namespace delta {

void CollectExprReads(const Expr* expr,
                      std::unordered_set<std::string_view>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    out.insert(expr->text);
    return;
  }
  CollectExprReads(expr->lhs, out);
  CollectExprReads(expr->rhs, out);
  CollectExprReads(expr->condition, out);
  CollectExprReads(expr->true_expr, out);
  CollectExprReads(expr->false_expr, out);
  CollectExprReads(expr->base, out);
  CollectExprReads(expr->index, out);
  for (auto* arg : expr->args) CollectExprReads(arg, out);
  for (auto* elem : expr->elements) CollectExprReads(elem, out);
}

void CollectStmtReads(const Stmt* stmt,
                      std::unordered_set<std::string_view>& out) {
  if (!stmt) return;
  CollectExprReads(stmt->condition, out);
  CollectExprReads(stmt->rhs, out);
  CollectExprReads(stmt->expr, out);
  CollectExprReads(stmt->for_cond, out);
  for (auto* s : stmt->stmts) CollectStmtReads(s, out);
  CollectStmtReads(stmt->then_branch, out);
  CollectStmtReads(stmt->else_branch, out);
  CollectStmtReads(stmt->for_body, out);
  CollectStmtReads(stmt->for_init, out);
  CollectStmtReads(stmt->for_step, out);
  CollectStmtReads(stmt->body, out);
  for (auto* s : stmt->fork_stmts) CollectStmtReads(s, out);
}

std::vector<std::string_view> CollectReadSignals(const Stmt* body) {
  std::unordered_set<std::string_view> set;
  CollectStmtReads(body, set);
  return {set.begin(), set.end()};
}

std::vector<EventExpr> InferSensitivity(const Stmt* body, Arena& arena) {
  auto signals = CollectReadSignals(body);
  std::vector<EventExpr> events;
  events.reserve(signals.size());
  for (auto name : signals) {
    auto* expr = arena.Create<Expr>();
    expr->kind = ExprKind::kIdentifier;
    expr->text = name;
    events.push_back({Edge::kNone, expr});
  }
  return events;
}

}  // namespace delta
