#include "elaborator/queue_dim.h"

#include <cstdint>
#include <optional>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "parser/ast.h"

namespace delta {

bool IsQueueDim(const Expr* dim) {
  return dim && dim->kind == ExprKind::kIdentifier && dim->text == "$";
}

std::optional<int32_t> QueueBoundMaxSize(int64_t bound) {
  if (bound <= 0) return std::nullopt;
  return static_cast<int32_t>(bound + 1);
}

static void CheckStmtQueueBound(const Stmt* s, const ScopeMap& scope,
                                DiagEngine& diag) {
  if (s->kind != StmtKind::kVarDecl || s->var_unpacked_dims.empty()) return;
  const auto* dim = s->var_unpacked_dims[0];
  if (!IsQueueDim(dim) || !dim->rhs) return;
  auto bound = ConstEvalInt(dim->rhs, scope);
  if (!bound || QueueBoundMaxSize(*bound)) return;
  diag.Error(s->range.start, "queue bound must be a positive integer",
             Subclause("7.10"));
}

void CheckBlockQueueBounds(const Stmt* s, const ScopeMap& scope,
                           DiagEngine& diag) {
  if (!s) return;
  CheckStmtQueueBound(s, scope, diag);
  for (const auto* sub : s->stmts) CheckBlockQueueBounds(sub, scope, diag);
  for (const auto* sub : s->fork_stmts) CheckBlockQueueBounds(sub, scope, diag);
  for (const auto* init : s->for_inits)
    CheckBlockQueueBounds(init, scope, diag);
  CheckBlockQueueBounds(s->then_branch, scope, diag);
  CheckBlockQueueBounds(s->else_branch, scope, diag);
  CheckBlockQueueBounds(s->body, scope, diag);
  CheckBlockQueueBounds(s->for_body, scope, diag);
  for (const auto& ci : s->case_items)
    CheckBlockQueueBounds(ci.body, scope, diag);
}

}  // namespace delta
