#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

template <typename Match>
static bool BodyContainsStmt(const Stmt* s, Match match) {
  if (!s) return false;
  if (match(s)) return true;
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (!found) found = BodyContainsStmt(sub, match);
  });
  return found;
}

static bool BodyContainsFork(const Stmt* s) {
  return BodyContainsStmt(
      s, [](const Stmt* n) { return n->kind == StmtKind::kFork; });
}

static bool BodyContainsNonblocking(const Stmt* s) {
  return BodyContainsStmt(
      s, [](const Stmt* n) { return n->kind == StmtKind::kNonblockingAssign; });
}

static bool SchedulesPostReturnEvent(const Stmt* s) {
  switch (s->kind) {
    case StmtKind::kDelay:
    case StmtKind::kCycleDelay:
    case StmtKind::kEventControl:
    case StmtKind::kTimingControl:
    case StmtKind::kWait:
    case StmtKind::kWaitFork:
    case StmtKind::kWaitOrder:
    case StmtKind::kEventTrigger:
    case StmtKind::kNbEventTrigger:
    case StmtKind::kExpect:
      return true;
    default:
      return false;
  }
}

static bool BodyContainsEventScheduling(const Stmt* s) {
  return BodyContainsStmt(s, SchedulesPostReturnEvent);
}

static void CollectLocalDeclNames(const Stmt* s,
                                  std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl) {
    if (!s->var_name.empty()) out.insert(s->var_name);
  }
  for (std::string_view name : ForHeaderDeclaredNames(s)) out.insert(name);
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CollectLocalDeclNames(sub, out); });
}

static const Expr* LeftmostIdentifier(const Expr* e) {
  while (e && e->kind == ExprKind::kMemberAccess) e = e->lhs;
  return e;
}

static bool IsBuiltinMethodOn(
    const Expr* call, const std::unordered_set<std::string_view>& names) {
  if (!call || call->kind != ExprKind::kCall) return false;
  if (!call->lhs || call->lhs->kind != ExprKind::kMemberAccess) return false;
  const Expr* root = LeftmostIdentifier(call->lhs);
  if (!root || root->kind != ExprKind::kIdentifier) return false;
  return names.count(root->text) > 0;
}

struct ConstFuncScope {
  const std::unordered_set<std::string_view>& param_names;
  const std::unordered_set<std::string_view>& function_names;
  const std::unordered_map<std::string_view, const ModuleItem*>* func_decls;
  std::unordered_set<std::string_view>* visited;
  DiagEngine& diag;
};

struct ConstFuncBodyCheck {
  std::string_view func_name;
  const std::unordered_set<std::string_view>& param_names;
  const std::unordered_set<std::string_view>& function_names;
  const std::unordered_set<std::string_view>& local_names;
  const std::unordered_map<std::string_view, const ModuleItem*>* func_decls;
  std::unordered_set<std::string_view>* visited;
  DiagEngine& diag;
  SourceLoc loc;
  bool failed = false;
};

static bool ValidateConstantFunction(const ModuleItem* func, SourceLoc loc,
                                     const ConstFuncScope& scope);

static void WalkConstFuncExpr(const Expr* e, ConstFuncBodyCheck& chk);

static void WalkConstFuncExprChildren(const Expr* e, ConstFuncBodyCheck& chk) {
  WalkConstFuncExpr(e->lhs, chk);
  WalkConstFuncExpr(e->rhs, chk);
  WalkConstFuncExpr(e->condition, chk);
  WalkConstFuncExpr(e->true_expr, chk);
  WalkConstFuncExpr(e->false_expr, chk);
  WalkConstFuncExpr(e->base, chk);
  WalkConstFuncExpr(e->index, chk);
  WalkConstFuncExpr(e->index_end, chk);
  WalkConstFuncExpr(e->repeat_count, chk);
  for (auto* a : e->args) WalkConstFuncExpr(a, chk);
  for (auto* el : e->elements) WalkConstFuncExpr(el, chk);
}

static void CheckConstFuncIdentifier(const Expr* e, ConstFuncBodyCheck& chk) {
  if (e->text == chk.func_name) return;
  if (chk.local_names.count(e->text)) return;
  if (chk.param_names.count(e->text)) return;
  if (chk.function_names.count(e->text)) return;
  chk.diag.Error(
      chk.loc,
      std::format(
          "constant function '{}' references identifier '{}' that is not "
          "a parameter, function name, or local declaration",
          chk.func_name, e->text),
      Subclause("13.4.3"));
  chk.failed = true;
}

static void CheckConstFuncMemberAccess(const Expr* e, ConstFuncBodyCheck& chk) {
  const Expr* root = LeftmostIdentifier(e);
  if (root && root->kind == ExprKind::kIdentifier &&
      !chk.local_names.count(root->text) &&
      !chk.param_names.count(root->text)) {
    chk.diag.Error(
        chk.loc,
        std::format("constant function '{}' uses a hierarchical reference, "
                    "which constant functions are barred from",
                    chk.func_name),
        Subclause("13.4.3"));
    chk.failed = true;
    return;
  }
  WalkConstFuncExprChildren(e, chk);
}

static void CheckConstFuncSystemCall(const Expr* e, ConstFuncBodyCheck& chk) {
  if (!IsConstantSysFunc(e->callee)) {
    chk.diag.Error(
        chk.loc,
        std::format("constant function '{}' calls non-constant system function "
                    "'{}'",
                    chk.func_name, e->callee),
        Subclause("13.4.3"));
    chk.failed = true;
    return;
  }
  WalkConstFuncExprChildren(e, chk);
}

static void CheckConstFuncCall(const Expr* e, ConstFuncBodyCheck& chk) {
  if (IsBuiltinMethodOn(e, chk.local_names) ||
      IsBuiltinMethodOn(e, chk.param_names)) {
    for (auto* a : e->args) WalkConstFuncExpr(a, chk);
    return;
  }
  if (!e->callee.empty() && !chk.function_names.count(e->callee) &&
      e->callee != chk.func_name) {
    chk.diag.Error(
        chk.loc,
        std::format(
            "constant function '{}' invokes '{}' which is not a constant "
            "function",
            chk.func_name, e->callee),
        Subclause("13.4.3"));
    chk.failed = true;
    return;
  }
  if (!e->callee.empty() && chk.func_decls && chk.visited &&
      e->callee != chk.func_name && !chk.visited->count(e->callee)) {
    auto it = chk.func_decls->find(e->callee);
    if (it != chk.func_decls->end()) {
      ConstFuncScope scope{chk.param_names, chk.function_names, chk.func_decls,
                           chk.visited, chk.diag};
      if (!ValidateConstantFunction(it->second, chk.loc, scope)) {
        chk.failed = true;
        return;
      }
    }
  }
  WalkConstFuncExprChildren(e, chk);
}

static void WalkConstFuncExpr(const Expr* e, ConstFuncBodyCheck& chk) {
  if (!e || chk.failed) return;
  switch (e->kind) {
    case ExprKind::kIdentifier:
      CheckConstFuncIdentifier(e, chk);
      return;
    case ExprKind::kMemberAccess:
      CheckConstFuncMemberAccess(e, chk);
      return;
    case ExprKind::kSystemCall:
      CheckConstFuncSystemCall(e, chk);
      return;
    case ExprKind::kCall:
      CheckConstFuncCall(e, chk);
      return;
    default:
      WalkConstFuncExprChildren(e, chk);
      return;
  }
}

static const Expr* StatementFormSystemCall(const Stmt* s) {
  if (s->kind != StmtKind::kExprStmt || !s->expr) return nullptr;
  return s->expr->kind == ExprKind::kSystemCall ? s->expr : nullptr;
}

static void WalkConstFuncStmt(const Stmt* s, ConstFuncBodyCheck& chk) {
  if (!s || chk.failed) return;
  const Expr* sys_call = StatementFormSystemCall(s);
  if (sys_call) {
    for (auto* a : sys_call->args) WalkConstFuncExpr(a, chk);
  }
  ForEachChildExpr(s, [&](Expr* const& e) {
    if (e != sys_call) WalkConstFuncExpr(e, chk);
  });
  ForEachChildStmt(s, [&](Stmt* const& sub) { WalkConstFuncStmt(sub, chk); });
}

static bool ValidateConstFuncArgs(
    const ModuleItem* func, SourceLoc loc,
    const std::unordered_set<std::string_view>& param_names, DiagEngine& diag) {
  ScopeMap default_scope;
  for (auto p : param_names) default_scope[p] = 0;
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kOutput ||
        arg.direction == Direction::kInout ||
        arg.direction == Direction::kRef) {
      diag.Error(loc,
                 std::format("constant function '{}' declares an argument of "
                             "direction {}, which constant functions are "
                             "barred from",
                             func->name,
                             arg.direction == Direction::kOutput  ? "output"
                             : arg.direction == Direction::kInout ? "inout"
                                                                  : "ref"),
                 Subclause("13.4.3"));
      return false;
    }
    if (arg.default_value &&
        !IsConstantExpr(arg.default_value, default_scope)) {
      diag.Error(
          loc,
          std::format(
              "constant function '{}' default value for argument '{}' is not "
              "a constant expression",
              func->name, arg.name),
          Subclause("13.4.3"));
      return false;
    }
  }
  return true;
}

static bool ValidateConstFuncBodyContent(const ModuleItem* func, SourceLoc loc,
                                         DiagEngine& diag) {
  for (auto* s : func->func_body_stmts) {
    if (BodyContainsFork(s)) {
      diag.Error(loc,
                 std::format("constant function '{}' uses fork, which "
                             "constant functions are barred from",
                             func->name),
                 Subclause("13.4.3"));
      return false;
    }
    if (BodyContainsNonblocking(s)) {
      diag.Error(loc,
                 std::format("constant function '{}' shall not contain "
                             "nonblocking assignments",
                             func->name),
                 Subclause("13.4.3"));
      return false;
    }
    if (BodyContainsEventScheduling(s)) {
      diag.Error(loc,
                 std::format(
                     "constant function '{}' schedules an event that would run "
                     "once it has returned, which constant functions are "
                     "barred from",
                     func->name),
                 Subclause("13.4.3"));
      return false;
    }
  }
  return true;
}

static std::unordered_set<std::string_view> CollectConstFuncLocalNames(
    const ModuleItem* func) {
  std::unordered_set<std::string_view> local_names;
  for (const auto& arg : func->func_args)
    if (!arg.name.empty()) local_names.insert(arg.name);
  if (!func->name.empty()) local_names.insert(func->name);
  for (auto* s : func->func_body_stmts) CollectLocalDeclNames(s, local_names);
  return local_names;
}

static bool CheckConstFuncBody(
    const ModuleItem* func, SourceLoc loc, const ConstFuncScope& scope,
    const std::unordered_set<std::string_view>& local_names) {
  ConstFuncBodyCheck chk{func->name,
                         scope.param_names,
                         scope.function_names,
                         local_names,
                         scope.func_decls,
                         scope.visited,
                         scope.diag,
                         loc,
                         false};
  for (auto* s : func->func_body_stmts) WalkConstFuncStmt(s, chk);
  return !chk.failed;
}

static bool ExprCallsSubroutine(const Expr* e) {
  if (e == nullptr) return false;
  return e->kind == ExprKind::kCall || AnyExprChild(e, ExprCallsSubroutine);
}

static bool StmtCallsInLocalParam(const Stmt* s) {
  if (s == nullptr) return false;
  if (s->kind == StmtKind::kVarDecl && s->var_is_param &&
      ExprCallsSubroutine(s->var_init))
    return true;
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    found = found || StmtCallsInLocalParam(sub);
  });
  return found;
}

static bool CheckNoCallInLocalParams(const ModuleItem* func, SourceLoc loc,
                                     DiagEngine& diag) {
  for (const Stmt* s : func->func_body_stmts) {
    if (!StmtCallsInLocalParam(s)) continue;
    diag.Error(loc,
               std::format("constant function '{}' calls a function in a "
                           "local parameter's initializer",
                           func->name),
               Subclause("13.4.3"));
    return false;
  }
  return true;
}

static bool ValidateConstantFunction(const ModuleItem* func, SourceLoc loc,
                                     const ConstFuncScope& scope) {
  if (scope.visited && !func->name.empty()) {
    if (!scope.visited->insert(func->name).second) return true;
  }
  if (!ValidateConstFuncArgs(func, loc, scope.param_names, scope.diag))
    return false;
  if (!ValidateConstFuncBodyContent(func, loc, scope.diag)) return false;
  if (!CheckNoCallInLocalParams(func, loc, scope.diag)) return false;

  std::unordered_set<std::string_view> local_names =
      CollectConstFuncLocalNames(func);
  return CheckConstFuncBody(func, loc, scope, local_names);
}

struct ConstFuncCallCtx {
  const std::unordered_map<std::string_view, const ModuleItem*>& func_decls;
  const std::unordered_set<std::string_view>& param_names;
  const std::unordered_set<std::string_view>& function_names;
  const std::unordered_set<std::string_view>& dpi_import_names;
  DiagEngine& diag;
  const std::unordered_set<std::string_view>* gen_funcs;
};

static void CheckConstFuncCallArgs(const Expr* expr, SourceLoc loc,
                                   const ConstFuncCallCtx& ctx) {
  ScopeMap arg_scope;
  for (auto p : ctx.param_names) arg_scope[p] = 0;
  for (auto* a : expr->args) {
    if (a && !IsConstantExpr(a, arg_scope)) {
      ctx.diag.Error(
          loc,
          std::format("constant function call '{}' has a non-constant argument",
                      expr->callee),
          Subclause("13.4.3"));
      break;
    }
  }
}

static void ValidateConstFuncCallNode(const Expr* expr, SourceLoc loc,
                                      const ConstFuncCallCtx& ctx) {
  if (ctx.gen_funcs != nullptr && ctx.gen_funcs->contains(expr->callee)) {
    ctx.diag.Error(loc,
                   std::format("function '{}' is declared inside a generate "
                               "block and is no constant function",
                               expr->callee),
                   Subclause("13.4.3"));
    return;
  }
  if (ctx.dpi_import_names.count(expr->callee)) {
    ctx.diag.Error(
        loc,
        std::format("DPI import '{}' shall not be used as a constant function",
                    expr->callee),
        Subclause("13.4.3"));
    return;
  }
  auto it = ctx.func_decls.find(expr->callee);
  if (it == ctx.func_decls.end()) return;
  std::unordered_set<std::string_view> visited;
  ConstFuncScope scope{ctx.param_names, ctx.function_names, &ctx.func_decls,
                       &visited, ctx.diag};
  ValidateConstantFunction(it->second, loc, scope);
  CheckConstFuncCallArgs(expr, loc, ctx);
}

static void ValidateConstantFuncCallsInExpr(const Expr* expr, SourceLoc loc,
                                            const ConstFuncCallCtx& ctx) {
  if (!expr || expr->kind == ExprKind::kTypeRef) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    ValidateConstFuncCallNode(expr, loc, ctx);
  }
  ValidateConstantFuncCallsInExpr(expr->lhs, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->rhs, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->condition, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->true_expr, loc, ctx);
  ValidateConstantFuncCallsInExpr(expr->false_expr, loc, ctx);
  for (auto* arg : expr->args) ValidateConstantFuncCallsInExpr(arg, loc, ctx);
  for (auto* elem : expr->elements)
    ValidateConstantFuncCallsInExpr(elem, loc, ctx);
}

static void ValidateConstFuncCallsInItems(const std::vector<ModuleItem*>& items,
                                          const ConstFuncCallCtx& ctx);

static void ValidateConstFuncCallsInBlock(const std::vector<ModuleItem*>& items,
                                          const ConstFuncCallCtx& ctx) {
  std::unordered_set<std::string_view> gen_funcs;
  if (ctx.gen_funcs != nullptr) gen_funcs = *ctx.gen_funcs;
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kFunctionDecl)
      gen_funcs.insert(item->name);
  }
  ConstFuncCallCtx inner = ctx;
  inner.gen_funcs = &gen_funcs;
  ValidateConstFuncCallsInItems(items, inner);
}

static void ValidateConstFuncCallsInGenerate(const ModuleItem* item,
                                             const ConstFuncCallCtx& ctx) {
  if (item->gen_cond) {
    ValidateConstantFuncCallsInExpr(item->gen_cond, item->loc, ctx);
  }
  ValidateConstFuncCallsInBlock(item->gen_body, ctx);
  if (item->gen_else) {
    ValidateConstFuncCallsInBlock(item->gen_else->gen_body, ctx);
  }
  for (const auto& ci : item->gen_case_items) {
    ValidateConstFuncCallsInBlock(ci.body, ctx);
  }
}

static void ValidateConstFuncCallsInItems(const std::vector<ModuleItem*>& items,
                                          const ConstFuncCallCtx& ctx) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
      ValidateConstantFuncCallsInExpr(item->init_expr, item->loc, ctx);
      continue;
    }
    if (item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase ||
        item->kind == ModuleItemKind::kGenerateFor) {
      ValidateConstFuncCallsInGenerate(item, ctx);
    }
  }
}

void Elaborator::ValidateConstantFunctionCalls(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> param_names;
  for (const auto& [pname, _] : decl->params) param_names.insert(pname);
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl && !item->name.empty())
      param_names.insert(item->name);
  }

  std::unordered_set<std::string_view> function_names;
  for (const auto& [fname, _] : func_decls_) function_names.insert(fname);

  std::unordered_set<std::string_view> dpi_import_names;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kDpiImport && !item->name.empty())
      dpi_import_names.insert(item->name);
  }

  ConstFuncCallCtx ctx{func_decls_,      param_names, function_names,
                       dpi_import_names, diag_,       nullptr};

  for (const auto& [name, default_expr] : decl->params) {
    if (default_expr) {
      ValidateConstantFuncCallsInExpr(default_expr, decl->range.start, ctx);
    }
  }
  ValidateConstFuncCallsInItems(decl->items, ctx);
}

}  // namespace delta
