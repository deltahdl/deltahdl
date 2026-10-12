#include "elaborator/default_pattern_values.h"

#include <cstddef>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// The parser keeps a keyed pattern's keys beside its elements, each key at the
// index of the value it introduces.
void CheckExpr(const Expr* e, DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kAssignmentPattern) {
    for (size_t i = 0; i < e->pattern_keys.size(); ++i) {
      const Expr* value = e->elements[i];
      if (e->pattern_keys[i]->text != "default" ||
          value->kind != ExprKind::kAssignmentPattern)
        continue;
      diag.Error(value->range.start,
                 "an untyped assignment pattern cannot be the value of a "
                 "default key",
                 Subclause("10.8"));
    }
  }
  ForEachExprChild(e, [&diag](const Expr* child) { CheckExpr(child, diag); });
}

void CheckStmt(const Stmt* s, DiagEngine& diag) {
  if (s == nullptr) return;
  ForEachChildExpr(s, [&diag](const Expr* e) { CheckExpr(e, diag); });
  ForEachChildStmt(s, [&diag](Stmt* const& sub) { CheckStmt(sub, diag); });
}

}  // namespace

void CheckUntypedDefaultPatternValues(const ModuleDecl* decl,
                                      DiagEngine& diag) {
  for (const auto& param : decl->params) CheckExpr(param.second, diag);
  for (const ModuleItem* item : decl->items) {
    CheckExpr(item->init_expr, diag);
    CheckExpr(item->assign_lhs, diag);
    CheckExpr(item->assign_rhs, diag);
    CheckStmt(item->body, diag);
    for (const Stmt* s : item->func_body_stmts) CheckStmt(s, diag);
  }
}

}  // namespace delta
