#include "parser/expr_substitute.h"

#include "common/arena.h"
#include "parser/ast_expr.h"

namespace delta {

Expr* SubstituteFormals(const Expr* e, const ActualsByFormal& actuals,
                        Arena& arena) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier) {
    auto it = actuals.find(e->text);
    if (it != actuals.end()) return it->second;
  }
  auto* copy = arena.Create<Expr>(*e);
  copy->lhs = SubstituteFormals(e->lhs, actuals, arena);
  copy->rhs = SubstituteFormals(e->rhs, actuals, arena);
  copy->condition = SubstituteFormals(e->condition, actuals, arena);
  copy->true_expr = SubstituteFormals(e->true_expr, actuals, arena);
  copy->false_expr = SubstituteFormals(e->false_expr, actuals, arena);
  copy->base = SubstituteFormals(e->base, actuals, arena);
  copy->index = SubstituteFormals(e->index, actuals, arena);
  copy->index_end = SubstituteFormals(e->index_end, actuals, arena);
  copy->with_expr = SubstituteFormals(e->with_expr, actuals, arena);
  copy->repeat_count = SubstituteFormals(e->repeat_count, actuals, arena);
  for (auto& sub : copy->elements) sub = SubstituteFormals(sub, actuals, arena);
  for (auto& sub : copy->args) sub = SubstituteFormals(sub, actuals, arena);
  return copy;
}

}  // namespace delta
