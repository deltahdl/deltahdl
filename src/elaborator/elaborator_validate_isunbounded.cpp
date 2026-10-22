// §20.6.3: the argument of $isunbounded is the name of a parameter.

#include <algorithm>
#include <cstddef>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

using ParamNames = std::unordered_set<std::string_view>;

// What the §20.6.3 walk reads besides the expression in hand: the parameters
// the module declares, the instance whose children a hierarchical name is read
// down, and where the reports go.
struct IsunboundedCtx {
  ParamNames params;
  const RtlirModule* mod;
  DiagEngine& diag;
};

// The instance below `scope` named `name`, or null where `scope` holds none.
const RtlirModule* ChildInstance(const RtlirModule* scope,
                                 std::string_view name) {
  for (const RtlirModuleInst& child : scope->children) {
    if (child.inst_name == name) return child.resolved;
  }
  return nullptr;
}

// Syntax 20-8's hierarchical_parameter_identifier: whether the hierarchical
// name `path`, read down the instances below `mod`, may name a parameter. It
// does where it ends at a parameter of the instance it reaches, and may where
// it reaches no instance this walk follows -- one starting above `mod`, one
// through a generate block, or one through a select of an instance array --
// which §23.8's checks resolve. A name that reaches an instance and ends at
// something else names no parameter.
bool MayNameHierParameter(const Expr* path, const RtlirModule* mod) {
  std::vector<std::string_view> names;
  const Expr* e = path;
  for (; e->kind == ExprKind::kMemberAccess; e = e->lhs) {
    names.push_back(e->rhs->text);
  }
  if (e->kind != ExprKind::kIdentifier) return true;
  names.push_back(e->text);
  const RtlirModule* scope = mod;
  for (size_t i = names.size() - 1; i > 0; --i) {
    scope = ChildInstance(scope, names[i]);
    if (scope == nullptr) return true;
  }
  return std::ranges::any_of(scope->params, [&](const RtlirParamDecl& p) {
    return p.name == names[0];
  });
}

// §20.6.3: a call of $isunbounded whose argument is not a name the module
// declares as a parameter, one a scope qualifies (`pkg::P`), nor a
// hierarchical name that may reach one (`s.P`), is an error.
void CheckIsunboundedExpr(const Expr* e, const IsunboundedCtx& ctx) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSystemCall && e->callee == "$isunbounded" &&
      e->args.size() == 1 && e->args[0] != nullptr) {
    const Expr* arg = e->args[0];
    bool names_param =
        (arg->kind == ExprKind::kIdentifier &&
         ctx.params.contains(arg->text)) ||
        (arg->kind == ExprKind::kMemberAccess &&
         (arg->is_scope_resolution || MayNameHierParameter(arg, ctx.mod)));
    if (!names_param) {
      ctx.diag.Error(arg->range.start,
                     "'$isunbounded' asks about a parameter, so its argument "
                     "must name one",
                     Subclause("20.6.3"));
    }
  }
  ForEachExprChild(
      e, [&](const Expr* child) { CheckIsunboundedExpr(child, ctx); });
}

// §20.6.3 names no position the call may stand in, so every expression a
// statement holds is one it is owed at.
void CheckIsunboundedStmt(const Stmt* s, const IsunboundedCtx& ctx) {
  if (s == nullptr) return;
  for (const Expr* e :
       {s->condition, s->lhs, s->rhs, s->expr, s->delay, s->var_init}) {
    CheckIsunboundedExpr(e, ctx);
  }
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CheckIsunboundedStmt(sub, ctx); });
}

}  // namespace

void CheckIsunboundedArgs(const ModuleDecl* decl, const RtlirModule* mod,
                          DiagEngine& diag) {
  IsunboundedCtx ctx{{}, mod, diag};
  for (const auto& [name, value] : decl->params) ctx.params.insert(name);
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl) ctx.params.insert(item->name);
  }
  for (const auto* item : decl->items) {
    CheckIsunboundedStmt(item->body, ctx);
    for (const Stmt* s : item->func_body_stmts) {
      CheckIsunboundedStmt(s, ctx);
    }
    CheckIsunboundedExpr(item->init_expr, ctx);
  }
}

}  // namespace delta
