#include "elaborator/type_ref_compare_fold.h"

#include <cstdint>
#include <optional>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator_validate_internal.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/parser_token_skips.h"

namespace delta {

// §6.23: a comparison of two type references is a constant expression, true
// exactly when the types match by §6.22.1, which only the elaborator's type
// tables can judge. Each one a procedure writes is handed to `fold`, which
// keeps its answer for the instance being elaborated, so the procedure reads
// its value; compared at run time by the names alone, `type(node) ==
// type(bit)` under `typedef bit node` was 0. The expression itself is left as
// written: every instance of the module shares it, and §6.20.3 lets each bind
// parameters that give the comparison another answer.
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

// Whether `e` writes an assignment operator, `(a = b)` or `(a += b)`.
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

// §11.3.6 (printed page 275): `fold` where an assignment operator is barred,
// outside a procedural statement and in a procedural continuous assignment. A
// comparison whose operand writes one is left whole for that rule's report.
TypeRefCompareFolder BarringAssignments(const TypeRefCompareFolder& fold) {
  return [&fold](const Expr* e) -> std::optional<int64_t> {
    if (WritesAnAssignment(e)) return std::nullopt;
    return fold(e);
  };
}

void FoldTypeRefComparesInStmt(Stmt* s, const TypeRefCompareFolder& fold) {
  if (s == nullptr) return;
  // §10.6: assign and force are the procedural continuous assignments.
  bool is_continuous =
      s->kind == StmtKind::kAssign || s->kind == StmtKind::kForce;
  FoldTypeRefComparesInExpr(s->rhs,
                            is_continuous ? BarringAssignments(fold) : fold);
  for (Expr* e : {s->lhs, s->expr, s->condition, s->assert_expr}) {
    FoldTypeRefComparesInExpr(e, fold);
  }
  // A declaration's initializer, a block parameter's value among them, is
  // not a procedural statement (§11.3.6).
  FoldTypeRefComparesInExpr(s->var_init, BarringAssignments(fold));
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { FoldTypeRefComparesInStmt(sub, fold); });
}

// The comparisons of type references `item` writes where a value is read while
// the design runs: its procedure's or subroutine's statements, a continuous
// assignment's right-hand side and a net's or variable's initializer. A
// parameter's value is folded by constant evaluation (TypedefRegistryGuard),
// and a let's body stands for its formals' actuals, which are not yet known.
void FoldItemTypeRefCompares(ModuleItem* item,
                             const TypeRefCompareFolder& fold) {
  FoldTypeRefComparesInStmt(item->body, fold);
  for (auto* s : item->func_body_stmts) FoldTypeRefComparesInStmt(s, fold);
  if (item->kind != ModuleItemKind::kContAssign &&
      item->kind != ModuleItemKind::kNetDecl &&
      item->kind != ModuleItemKind::kVarDecl)
    return;
  TypeRefCompareFolder outside_procedures = BarringAssignments(fold);
  FoldTypeRefComparesInExpr(item->assign_rhs, outside_procedures);
  FoldTypeRefComparesInExpr(item->init_expr, outside_procedures);
}

}  // namespace delta
