#include "elaboration/sensitivity.h"

#include "common/arena.h"
#include "elaboration/const_eval.h"
#include "parser/ast.h"

namespace delta {

// §9.2.2.2.1 / §11.5.3: For select expressions, insert the longest static
// prefix as the sensitivity signal.  Non-static index sub-expressions are
// also collected (they are themselves reads).
static void CollectSelectReads(const Expr* expr,
                               std::unordered_set<std::string>& out) {
  out.insert(LongestStaticPrefix(expr));
  // Walk the index chain to collect reads from non-static indices.
  const Expr* cur = expr;
  while (cur && cur->kind == ExprKind::kSelect) {
    if (cur->index && cur->index->kind != ExprKind::kIntegerLiteral) {
      CollectExprReads(cur->index, out);
    }
    cur = cur->base;
  }
}

void CollectExprReads(const Expr* expr,
                      std::unordered_set<std::string>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    out.insert(std::string(expr->text));
    return;
  }
  if (expr->kind == ExprKind::kSelect) {
    CollectSelectReads(expr, out);
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
                      std::unordered_set<std::string>& out) {
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

std::vector<std::string> CollectReadSignals(const Stmt* body) {
  std::unordered_set<std::string> set;
  CollectStmtReads(body, set);
  return {set.begin(), set.end()};
}

std::vector<EventExpr> InferSensitivity(const Stmt* body, Arena& arena) {
  auto signals = CollectReadSignals(body);
  std::vector<EventExpr> events;
  events.reserve(signals.size());
  for (const auto& name : signals) {
    auto* expr = arena.Create<Expr>();
    expr->kind = ExprKind::kIdentifier;
    expr->text = std::string_view(
        arena.AllocString(name.data(), name.size()), name.size());
    events.push_back({Edge::kNone, expr});
  }
  return events;
}

}  // namespace delta
