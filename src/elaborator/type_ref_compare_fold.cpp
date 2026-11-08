#include "elaborator/type_ref_compare_fold.h"

#include <cstdint>
#include <optional>

#include "elaborator/const_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/parser_token_skips.h"

namespace delta {

void FoldTypeRefComparesInExpr(Expr* e, const TypeRefCompareFolder& fold) {
  if (e == nullptr) return;
  if (IsTypeRefComparison(e) && fold(e).has_value()) return;
  for (Expr* sub :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr}) {
    FoldTypeRefComparesInExpr(sub, fold);
  }
  for (Expr* elem : e->elements) FoldTypeRefComparesInExpr(elem, fold);
  for (Expr* arg : e->args) FoldTypeRefComparesInExpr(arg, fold);
}

bool WritesAnAssignment(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kBinary &&
      (e->op == TokenKind::kEq || IsCompoundAssignOp(e->op)))
    return true;
  for (const Expr* sub :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr}) {
    if (WritesAnAssignment(sub)) return true;
  }
  for (const Expr* elem : e->elements) {
    if (WritesAnAssignment(elem)) return true;
  }
  for (const Expr* arg : e->args) {
    if (WritesAnAssignment(arg)) return true;
  }
  return false;
}

TypeRefCompareFolder BarringAssignments(const TypeRefCompareFolder& fold) {
  return [&fold](const Expr* e) -> std::optional<int64_t> {
    if (WritesAnAssignment(e)) return std::nullopt;
    return fold(e);
  };
}

void FoldTypeRefComparesOfStmt(Stmt* s, const TypeRefCompareFolder& fold) {
  bool is_continuous =
      s->kind == StmtKind::kAssign || s->kind == StmtKind::kForce;
  FoldTypeRefComparesInExpr(s->rhs,
                            is_continuous ? BarringAssignments(fold) : fold);
  for (Expr* e : {s->lhs, s->expr, s->condition, s->assert_expr}) {
    FoldTypeRefComparesInExpr(e, fold);
  }
  for (CaseItem& item : s->case_items) {
    for (Expr* pattern : item.patterns) {
      FoldTypeRefComparesInExpr(pattern, fold);
    }
  }
  FoldTypeRefComparesInExpr(s->var_init, BarringAssignments(fold));
}

void FoldItemTypeRefCompares(ModuleItem* item,
                             const TypeRefCompareFolder& fold) {
  if (item->kind != ModuleItemKind::kContAssign &&
      item->kind != ModuleItemKind::kNetDecl &&
      item->kind != ModuleItemKind::kVarDecl)
    return;
  TypeRefCompareFolder outside_procedures = BarringAssignments(fold);
  FoldTypeRefComparesInExpr(item->assign_rhs, outside_procedures);
  FoldTypeRefComparesInExpr(item->init_expr, outside_procedures);
}

}  // namespace delta
