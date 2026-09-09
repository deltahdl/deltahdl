#pragma once

#include "parser/ast_expr.h"

namespace delta {

// Every node of `e`, itself included. Three walks ask a question of every
// subexpression -- two in the lowerer, about the calls and the names an
// assertion's property makes, and one in the assertion executor, about the
// §16.9.4 future sampled value functions it names -- so the descent they share
// is written once here rather than three times.
template <typename Fn>
void ForEachSubExpr(const Expr* e, const Fn& fn) {
  if (e == nullptr) return;
  fn(e);
  ForEachSubExpr(e->lhs, fn);
  ForEachSubExpr(e->rhs, fn);
  ForEachSubExpr(e->condition, fn);
  ForEachSubExpr(e->true_expr, fn);
  ForEachSubExpr(e->false_expr, fn);
  ForEachSubExpr(e->base, fn);
  ForEachSubExpr(e->index, fn);
  ForEachSubExpr(e->index_end, fn);
  ForEachSubExpr(e->with_expr, fn);
  ForEachSubExpr(e->repeat_count, fn);
  for (auto* sub : e->elements) ForEachSubExpr(sub, fn);
  for (auto* sub : e->args) ForEachSubExpr(sub, fn);
}

}  // namespace delta
