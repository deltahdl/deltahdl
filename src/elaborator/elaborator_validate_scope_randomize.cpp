#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

bool IsScopeRandomizeCall(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* lhs = expr->lhs;
  if (!lhs) return false;
  if (lhs->kind == ExprKind::kIdentifier && lhs->text == "randomize") {
    return true;
  }
  if (lhs->kind == ExprKind::kMemberAccess && lhs->rhs &&
      lhs->rhs->kind == ExprKind::kIdentifier &&
      lhs->rhs->text == "randomize" && lhs->lhs &&
      lhs->lhs->kind == ExprKind::kIdentifier && lhs->lhs->text == "std") {
    return true;
  }
  return false;
}

bool IsStdQualifiedRandomizeCall(const Expr* expr) {
  return expr->lhs && expr->lhs->kind == ExprKind::kMemberAccess;
}

void CheckScopeRandomizeArguments(const Expr* expr, DiagEngine& diag) {
  for (const auto* arg : expr->args) {
    if (!arg) continue;
    if (arg->kind == ExprKind::kIdentifier && arg->text == "null") {
      diag.Error(arg->range.start,
                 "'null' is not a legal argument to a scope randomize call",
                 Subclause("A.8.2"));
    } else if (arg->kind != ExprKind::kIdentifier) {
      const bool kStd = IsStdQualifiedRandomizeCall(expr);
      diag.Error(arg->range.start,
                 kStd ? "argument to std::randomize shall be a variable "
                        "identifier"
                      : "argument to a scope randomize call shall be a "
                        "variable identifier",
                 Subclause(kStd ? "G.5" : "A.8.2"));
    }
  }
}

void CheckScopeRandomizeRulesInExpr(const Expr* expr, DiagEngine& diag) {
  if (!expr) return;
  if (IsScopeRandomizeCall(expr)) {
    CheckScopeRandomizeArguments(expr, diag);
    if (expr->with_has_parens) {
      diag.Error(expr->range.start,
                 "scope randomize call cannot use a parenthesized identifier "
                 "list after 'with'",
                 Subclause("A.8.2"));
    }
  }
  CheckScopeRandomizeRulesInExpr(expr->lhs, diag);
  CheckScopeRandomizeRulesInExpr(expr->rhs, diag);
  CheckScopeRandomizeRulesInExpr(expr->condition, diag);
  CheckScopeRandomizeRulesInExpr(expr->true_expr, diag);
  CheckScopeRandomizeRulesInExpr(expr->false_expr, diag);
  CheckScopeRandomizeRulesInExpr(expr->base, diag);
  CheckScopeRandomizeRulesInExpr(expr->index, diag);
  CheckScopeRandomizeRulesInExpr(expr->index_end, diag);
  for (const auto* a : expr->args) CheckScopeRandomizeRulesInExpr(a, diag);
  for (const auto* e : expr->elements) CheckScopeRandomizeRulesInExpr(e, diag);
}

void WalkStmtForScopeRandomize(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  CheckScopeRandomizeRulesInExpr(s->expr, diag);
  CheckScopeRandomizeRulesInExpr(s->lhs, diag);
  CheckScopeRandomizeRulesInExpr(s->rhs, diag);
  CheckScopeRandomizeRulesInExpr(s->condition, diag);
  CheckScopeRandomizeRulesInExpr(s->for_cond, diag);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtForScopeRandomize(sub, diag); });
}

void ValidateScopeRandomizeInDecl(const ModuleDecl* decl, DiagEngine& diag) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      WalkStmtForScopeRandomize(item->body, diag);
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (const auto* s : item->func_body_stmts)
        WalkStmtForScopeRandomize(s, diag);
    }
  }
}

}  // namespace

void Elaborator::ValidateScopeRandomizeCalls(const ModuleDecl* decl) {
  ValidateScopeRandomizeInDecl(decl, diag_);
}

}  // namespace delta
