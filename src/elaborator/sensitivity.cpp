#include "elaborator/sensitivity.h"

#include "common/arena.h"
#include "elaborator/const_eval.h"
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

void CollectExprReads(const Expr* expr, std::unordered_set<std::string>& out) {
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

void CollectStmtReads(const Stmt* stmt, std::unordered_set<std::string>& out) {
  if (!stmt) return;
  CollectExprReads(stmt->condition, out);
  CollectExprReads(stmt->rhs, out);
  CollectExprReads(stmt->expr, out);
  CollectExprReads(stmt->for_cond, out);
  for (auto* s : stmt->stmts) CollectStmtReads(s, out);
  CollectStmtReads(stmt->then_branch, out);
  CollectStmtReads(stmt->else_branch, out);
  CollectStmtReads(stmt->for_body, out);
  for (auto* fi : stmt->for_inits) CollectStmtReads(fi, out);
  for (auto* fs : stmt->for_steps) CollectStmtReads(fs, out);
  CollectStmtReads(stmt->body, out);
  for (auto* s : stmt->fork_stmts) CollectStmtReads(s, out);
  // §9.2.2.2.2: Case item patterns and bodies contribute to sensitivity.
  for (const auto& ci : stmt->case_items) {
    for (const auto* pat : ci.patterns) CollectExprReads(pat, out);
    CollectStmtReads(ci.body, out);
  }
  // §9.2.2.2.2: Immediate assertion expressions contribute to sensitivity.
  CollectExprReads(stmt->assert_expr, out);
  CollectStmtReads(stmt->assert_pass_stmt, out);
  CollectStmtReads(stmt->assert_fail_stmt, out);
}

std::vector<std::string> CollectReadSignals(const Stmt* body) {
  std::unordered_set<std::string> set;
  CollectStmtReads(body, set);
  return {set.begin(), set.end()};
}

// §9.2.2.2.1(b): Extract the base identifier name from an assignment LHS.
static void CollectAssignLhsName(const Expr* lhs,
                                 std::unordered_set<std::string>& out) {
  if (!lhs) return;
  const Expr* e = lhs;
  while (e->kind == ExprKind::kSelect && e->base) e = e->base;
  if (e->kind == ExprKind::kIdentifier && !e->text.empty())
    out.insert(std::string(e->text));
}

// §9.2.2.2.1(b): Collect LHS variable names written in the statement tree.
void CollectWrittenNames(const Stmt* stmt,
                         std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    CollectAssignLhsName(stmt->lhs, out);
  }
  for (const auto* s : stmt->stmts) CollectWrittenNames(s, out);
  CollectWrittenNames(stmt->then_branch, out);
  CollectWrittenNames(stmt->else_branch, out);
  CollectWrittenNames(stmt->body, out);
  CollectWrittenNames(stmt->for_body, out);
  for (auto* fi : stmt->for_inits) CollectWrittenNames(fi, out);
  for (auto* fs : stmt->for_steps) CollectWrittenNames(fs, out);
  for (const auto& ci : stmt->case_items) CollectWrittenNames(ci.body, out);
  for (const auto* s : stmt->fork_stmts) CollectWrittenNames(s, out);
}

// §9.2.2.2.1(a): Collect names of variables declared within the block.
static void CollectBlockLocalNames(const Stmt* stmt,
                                   std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kVarDecl && !stmt->var_name.empty()) {
    out.insert(std::string(stmt->var_name));
  }
  for (const auto* s : stmt->stmts) CollectBlockLocalNames(s, out);
  CollectBlockLocalNames(stmt->then_branch, out);
  CollectBlockLocalNames(stmt->else_branch, out);
  CollectBlockLocalNames(stmt->body, out);
  CollectBlockLocalNames(stmt->for_body, out);
  for (const auto& ci : stmt->case_items) CollectBlockLocalNames(ci.body, out);
}

std::vector<EventExpr> InferSensitivity(const Stmt* body, Arena& arena) {
  auto signals = CollectReadSignals(body);

  // §9.2.2.2.1(a): Exclude variables declared within the block.
  std::unordered_set<std::string> locals;
  CollectBlockLocalNames(body, locals);

  // §9.2.2.2.1(b): Exclude variables also written within the block.
  std::unordered_set<std::string> written;
  CollectWrittenNames(body, written);

  std::vector<EventExpr> events;
  events.reserve(signals.size());
  for (const auto& name : signals) {
    if (locals.count(name)) continue;
    if (written.count(name)) continue;
    auto* expr = arena.Create<Expr>();
    expr->kind = ExprKind::kIdentifier;
    expr->text = std::string_view(arena.AllocString(name.data(), name.size()),
                                  name.size());
    events.push_back({Edge::kNone, expr});
  }
  return events;
}

}  // namespace delta
