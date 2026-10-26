#include "elaborator/implication_operator_rules.h"

#include <format>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// Whether the statement `stmt` holds a property in its own expressions rather
// than ordinary ones: a concurrent assertion or an expect statement in
// procedural code, which the parser marks is_procedural_concurrent, or the
// statement it builds for a static concurrent assertion's clocked boolean
// form, which it marks is_concurrent_clocked.
bool HoldsProperty(const Stmt& stmt) {
  return stmt.is_procedural_concurrent || stmt.is_concurrent_clocked;
}

void ReportStmtImplicationOperators(const Stmt* stmt, DiagEngine& diag) {
  if (stmt == nullptr) return;
  if (!HoldsProperty(*stmt)) {
    ForEachChildExpr(stmt, [&diag](const Expr* expr) {
      ReportImplicationOperators(expr, diag);
    });
  }
  ForEachChildStmt(stmt, [&diag](const Stmt* sub) {
    ReportStmtImplicationOperators(sub, diag);
  });
}

}  // namespace

void ReportImplicationOperators(const Expr* expr, DiagEngine& diag) {
  auto report = [&diag](const Expr* sub) {
    if (sub->kind != ExprKind::kBinary) return;
    if (sub->op != TokenKind::kPipeDashGt && sub->op != TokenKind::kPipeEqGt) {
      return;
    }
    // An item elaborated more than once, in each instance of its module or of
    // a loop generate block, is reported once.
    diag.ErrorOnce(
        sub->range.start,
        std::format(
            "the property operator '{}' joins the operands of an ordinary "
            "expression",
            sub->op == TokenKind::kPipeDashGt ? "|->" : "|=>"),
        Subclause("A.8.6"));
  };
  ForEachExprUnder(expr, report);
}

void ReportItemImplicationOperators(const ModuleItem& item, DiagEngine& diag) {
  switch (item.kind) {
    case ModuleItemKind::kContAssign:
      ReportImplicationOperators(item.assign_lhs, diag);
      ReportImplicationOperators(item.assign_rhs, diag);
      break;
    case ModuleItemKind::kNetDecl:
    case ModuleItemKind::kVarDecl:
    case ModuleItemKind::kParamDecl:
      ReportImplicationOperators(item.init_expr, diag);
      break;
    default:
      break;
  }
  ReportStmtImplicationOperators(item.body, diag);
  for (const Stmt* stmt : item.func_body_stmts) {
    ReportStmtImplicationOperators(stmt, diag);
  }
}

}  // namespace delta
