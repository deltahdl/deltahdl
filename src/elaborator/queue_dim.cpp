#include "elaborator/queue_dim.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

bool IsQueueDim(const Expr* dim) {
  return dim && dim->kind == ExprKind::kIdentifier && dim->text == "$";
}

uint32_t QueueLevelsFrom(const std::vector<Expr*>& dims, size_t first) {
  if (first >= dims.size()) return 0;
  for (size_t i = first; i < dims.size(); ++i) {
    if (dims[i] != nullptr && !IsQueueDim(dims[i])) return 0;
  }
  return static_cast<uint32_t>(dims.size() - first);
}

std::optional<int32_t> QueueBoundMaxSize(int64_t bound) {
  if (bound <= 0) return std::nullopt;
  return static_cast<int32_t>(bound + 1);
}

int32_t QueueDimMaxSize(const Expr* dim) {
  if (!IsQueueDim(dim) || dim->rhs == nullptr) return -1;
  return ConstEvalInt(dim->rhs).and_then(QueueBoundMaxSize).value_or(-1);
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
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckBlockQueueBounds(sub, scope, diag); });
}

}  // namespace delta
