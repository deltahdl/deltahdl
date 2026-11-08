#pragma once

#include <initializer_list>

#include "parser/ast_expr.h"

namespace delta {

template <typename Fn, typename Descends>
void ForEachSubExprWhere(const Expr* e, const Fn& fn,
                         const Descends& descends) {
  if (e == nullptr) return;
  fn(e);
  if (!descends(e)) return;
  for (const Expr* sub : {e->lhs, e->rhs, e->condition, e->true_expr,
                          e->false_expr, e->base, e->index, e->index_end,
                          e->with_expr, e->stream_range, e->repeat_count}) {
    ForEachSubExprWhere(sub, fn, descends);
  }
  for (auto* sub : e->elements) ForEachSubExprWhere(sub, fn, descends);
  for (auto* sub : e->args) ForEachSubExprWhere(sub, fn, descends);
}

template <typename Fn>
void ForEachSubExpr(const Expr* e, const Fn& fn) {
  ForEachSubExprWhere(e, fn, [](const Expr*) { return true; });
}

template <typename Fn>
void ForEachEvaluatedSubExpr(const Expr* e, const Fn& fn) {
  ForEachSubExprWhere(
      e, fn, [](const Expr* node) { return node->kind != ExprKind::kTypeRef; });
}

}  // namespace delta
