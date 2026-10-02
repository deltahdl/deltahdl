// §20.6.3: the argument of $isunbounded is the name of a parameter.

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

using ParamNames = std::unordered_set<std::string_view>;

// §20.6.3: a call of $isunbounded whose argument is not a name the module
// declares as a parameter, nor one a scope qualifies (`pkg::P`), is an error.
void CheckIsunboundedExpr(const Expr* e, const ParamNames& params,
                          DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSystemCall && e->callee == "$isunbounded" &&
      e->args.size() == 1 && e->args[0] != nullptr) {
    const Expr* arg = e->args[0];
    bool names_param =
        (arg->kind == ExprKind::kIdentifier && params.contains(arg->text)) ||
        (arg->kind == ExprKind::kMemberAccess && arg->is_scope_resolution);
    if (!names_param) {
      diag.Error(arg->range.start,
                 "the argument of '$isunbounded' shall be the name of a "
                 "parameter",
                 Subclause("20.6.3"));
    }
  }
  ForEachExprChild(
      e, [&](const Expr* child) { CheckIsunboundedExpr(child, params, diag); });
}

// §20.6.3 names no position the call may stand in, so every expression a
// statement holds is one it is owed at.
void CheckIsunboundedStmt(const Stmt* s, const ParamNames& params,
                          DiagEngine& diag) {
  if (s == nullptr) return;
  for (const Expr* e :
       {s->condition, s->lhs, s->rhs, s->expr, s->delay, s->var_init}) {
    CheckIsunboundedExpr(e, params, diag);
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckIsunboundedStmt(sub, params, diag); });
}

}  // namespace

void CheckIsunboundedArgs(const ModuleDecl* decl, DiagEngine& diag) {
  ParamNames params;
  for (const auto& [name, value] : decl->params) params.insert(name);
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl) params.insert(item->name);
  }
  for (const auto* item : decl->items) {
    CheckIsunboundedStmt(item->body, params, diag);
    for (const Stmt* s : item->func_body_stmts) {
      CheckIsunboundedStmt(s, params, diag);
    }
    CheckIsunboundedExpr(item->init_expr, params, diag);
  }
}

}  // namespace delta
