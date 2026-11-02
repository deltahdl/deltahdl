#pragma once

#include <initializer_list>

#include "parser/ast_expr.h"

namespace delta {

// Every node of `e`, itself included, descending below a node only where
// `descends` says so of it.
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

// Every node of `e`, itself included. Three walks ask a question of every
// subexpression -- two in the lowerer, about the calls and the names an
// assertion's property makes, and one in the assertion executor, about the
// §16.9.4 future sampled value functions it names -- so the descent they share
// is written once here rather than three times.
template <typename Fn>
void ForEachSubExpr(const Expr* e, const Fn& fn) {
  ForEachSubExprWhere(e, fn, [](const Expr*) { return true; });
}

// Every node of `e` that evaluating `e` reads. §6.23: a type reference stands
// for its operand's type and never evaluates the operand, so the walk visits
// the type reference itself and nothing it holds.
template <typename Fn>
void ForEachEvaluatedSubExpr(const Expr* e, const Fn& fn) {
  ForEachSubExprWhere(
      e, fn, [](const Expr* node) { return node->kind != ExprKind::kTypeRef; });
}

}  // namespace delta
