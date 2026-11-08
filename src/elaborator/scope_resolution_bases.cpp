#include "elaborator/scope_resolution_bases.h"

#include <vector>

#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

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
  CollectScopeBases(e->stream_range, out);
  for (const auto* a : e->args) CollectScopeBases(a, out);
  for (const auto* el : e->elements) CollectScopeBases(el, out);
}

void CollectProcScopeBases(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CollectScopeBases(s->rhs, out);
  }
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CollectProcScopeBases(sub, out); });
}

}  // namespace delta
