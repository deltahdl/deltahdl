#include "elaborator/implication_operator_rules.h"

#include <format>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

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
  // A let, typedef, nettype or import among a block's items is carried over
  // the item its declaration makes; a let's body is an expression.
  if (stmt->kind == StmtKind::kBlockItemDecl) {
    ReportItemImplicationOperators(*stmt->decl_item, diag);
  }
  if (!HoldsProperty(*stmt)) {
    ForEachChildExpr(stmt, [&diag](const Expr* expr) {
      ReportImplicationOperators(expr, diag);
    });
  }
  ForEachChildStmt(stmt, [&diag](const Stmt* sub) {
    ReportStmtImplicationOperators(sub, diag);
  });
}

// A class member's initializer and constraints, and its method's or nested
// class's expressions. A constraint is built from expressions (A.1.10); the
// implication it does hold is `->`.
void ReportMemberImplicationOperators(const ClassMember& member,
                                      DiagEngine& diag) {
  ReportImplicationOperators(member.init_expr, diag);
  for (const Expr* expr : member.constraint_exprs) {
    ReportImplicationOperators(expr, diag);
  }
  for (const Expr* expr : member.constraint_soft_exprs) {
    ReportImplicationOperators(expr, diag);
  }
  if (member.method != nullptr) {
    ReportItemImplicationOperators(*member.method, diag);
  }
  ReportClassImplicationOperators(member.nested_class, diag);
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

void ReportClassImplicationOperators(const ClassDecl* cls, DiagEngine& diag) {
  if (cls == nullptr) return;
  for (const auto& param : cls->params) {
    ReportImplicationOperators(param.second, diag);
  }
  for (const Expr* arg : cls->extends_args) {
    ReportImplicationOperators(arg, diag);
  }
  for (const ClassMember* member : cls->members) {
    ReportMemberImplicationOperators(*member, diag);
  }
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
    case ModuleItemKind::kLetDecl:
      ReportImplicationOperators(item.init_expr, diag);
      break;
    case ModuleItemKind::kClassDecl:
      ReportClassImplicationOperators(item.class_decl, diag);
      break;
    default:
      break;
  }
  // A subroutine's or a let's port defaults (A.2.7, A.2.12).
  for (const FunctionArg& arg : item.func_args) {
    ReportImplicationOperators(arg.default_value, diag);
  }
  ReportStmtImplicationOperators(item.body, diag);
  for (const Stmt* stmt : item.func_body_stmts) {
    ReportStmtImplicationOperators(stmt, diag);
  }
}

}  // namespace delta
