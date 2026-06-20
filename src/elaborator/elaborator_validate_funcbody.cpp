#include <format>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag);
void ValidateConstRefWriteProtection(const ModuleItem* func, DiagEngine& diag);

static void CheckNoReturnInFork(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn) {
    diag.Error(s->range.start,
               "return statement is not allowed inside a fork-join block");
    return;
  }
  for (auto* sub : s->stmts) CheckNoReturnInFork(sub, diag);
  for (auto* sub : s->fork_stmts) CheckNoReturnInFork(sub, diag);
  CheckNoReturnInFork(s->then_branch, diag);
  CheckNoReturnInFork(s->else_branch, diag);
  CheckNoReturnInFork(s->body, diag);
  CheckNoReturnInFork(s->for_body, diag);
  for (auto& ci : s->case_items) CheckNoReturnInFork(ci.body, diag);
  for (auto& ri : s->randcase_items) CheckNoReturnInFork(ri.second, diag);
  CheckNoReturnInFork(s->assert_pass_stmt, diag);
  CheckNoReturnInFork(s->assert_fail_stmt, diag);
}

static void CheckExprForRefArgs(
    const Expr* e, const std::unordered_set<std::string_view>& ref_names,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier && ref_names.count(e->text)) {
    diag.Error(e->range.start,
               std::format("ref argument '{}' cannot be used inside a "
                           "fork-join_any or fork-join_none block",
                           e->text));
    return;
  }
  CheckExprForRefArgs(e->lhs, ref_names, diag);
  CheckExprForRefArgs(e->rhs, ref_names, diag);
  CheckExprForRefArgs(e->condition, ref_names, diag);
  CheckExprForRefArgs(e->true_expr, ref_names, diag);
  CheckExprForRefArgs(e->false_expr, ref_names, diag);
  CheckExprForRefArgs(e->base, ref_names, diag);
  CheckExprForRefArgs(e->index, ref_names, diag);
  CheckExprForRefArgs(e->index_end, ref_names, diag);
  CheckExprForRefArgs(e->with_expr, ref_names, diag);
  CheckExprForRefArgs(e->repeat_count, ref_names, diag);
  for (auto* arg : e->args) CheckExprForRefArgs(arg, ref_names, diag);
  for (auto* elem : e->elements) CheckExprForRefArgs(elem, ref_names, diag);
}

static void CheckStmtExprsForRefArgs(
    const Stmt* s, const std::unordered_set<std::string_view>& ref_names,
    bool is_fork_block_item, DiagEngine& diag) {
  if (!is_fork_block_item || s->kind != StmtKind::kVarDecl)
    CheckExprForRefArgs(s->var_init, ref_names, diag);
  CheckExprForRefArgs(s->expr, ref_names, diag);
  CheckExprForRefArgs(s->lhs, ref_names, diag);
  CheckExprForRefArgs(s->rhs, ref_names, diag);
  CheckExprForRefArgs(s->delay, ref_names, diag);
  CheckExprForRefArgs(s->cycle_delay, ref_names, diag);
  CheckExprForRefArgs(s->condition, ref_names, diag);
  CheckExprForRefArgs(s->for_cond, ref_names, diag);
  CheckExprForRefArgs(s->assert_expr, ref_names, diag);
  CheckExprForRefArgs(s->repeat_event_count, ref_names, diag);
  for (auto* dim : s->var_unpacked_dims)
    CheckExprForRefArgs(dim, ref_names, diag);
  for (auto& ev : s->events) {
    CheckExprForRefArgs(ev.signal, ref_names, diag);
    CheckExprForRefArgs(ev.iff_condition, ref_names, diag);
  }
  for (auto& ci : s->case_items)
    for (auto* p : ci.patterns) CheckExprForRefArgs(p, ref_names, diag);
  for (auto& ri : s->randcase_items)
    CheckExprForRefArgs(ri.first, ref_names, diag);
  for (auto* we : s->wait_order_events)
    CheckExprForRefArgs(we, ref_names, diag);
}

static void CheckStmtForRefArgs(
    const Stmt* s, const std::unordered_set<std::string_view>& ref_names,
    bool is_fork_block_item, DiagEngine& diag) {
  if (!s) return;
  CheckStmtExprsForRefArgs(s, ref_names, is_fork_block_item, diag);
  for (auto* sub : s->stmts) CheckStmtForRefArgs(sub, ref_names, false, diag);
  for (auto* sub : s->fork_stmts)
    CheckStmtForRefArgs(sub, ref_names, false, diag);
  CheckStmtForRefArgs(s->then_branch, ref_names, false, diag);
  CheckStmtForRefArgs(s->else_branch, ref_names, false, diag);
  CheckStmtForRefArgs(s->body, ref_names, false, diag);
  CheckStmtForRefArgs(s->for_body, ref_names, false, diag);
  for (auto* init : s->for_inits)
    CheckStmtForRefArgs(init, ref_names, false, diag);
  for (auto* step : s->for_steps)
    CheckStmtForRefArgs(step, ref_names, false, diag);
  for (auto& ci : s->case_items)
    CheckStmtForRefArgs(ci.body, ref_names, false, diag);
  for (auto& ri : s->randcase_items)
    CheckStmtForRefArgs(ri.second, ref_names, false, diag);
  CheckStmtForRefArgs(s->assert_pass_stmt, ref_names, false, diag);
  CheckStmtForRefArgs(s->assert_fail_stmt, ref_names, false, diag);
}

static void CheckRefArgsInForkBlocks(
    const Stmt* s, const std::unordered_set<std::string_view>& ref_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kFork && (s->join_kind == TokenKind::kKwJoinAny ||
                                     s->join_kind == TokenKind::kKwJoinNone)) {
    for (auto* fs : s->fork_stmts) {
      bool is_block_item = (fs->kind == StmtKind::kVarDecl);
      CheckStmtForRefArgs(fs, ref_names, is_block_item, diag);
    }
  }
  for (auto* sub : s->stmts) CheckRefArgsInForkBlocks(sub, ref_names, diag);
  for (auto* sub : s->fork_stmts)
    CheckRefArgsInForkBlocks(sub, ref_names, diag);
  CheckRefArgsInForkBlocks(s->then_branch, ref_names, diag);
  CheckRefArgsInForkBlocks(s->else_branch, ref_names, diag);
  CheckRefArgsInForkBlocks(s->body, ref_names, diag);
  CheckRefArgsInForkBlocks(s->for_body, ref_names, diag);
  for (auto& ci : s->case_items)
    CheckRefArgsInForkBlocks(ci.body, ref_names, diag);
  for (auto& ri : s->randcase_items)
    CheckRefArgsInForkBlocks(ri.second, ref_names, diag);
}

static void CheckFuncBodyStmtSelf(
    const Stmt* s, bool is_void,
    const std::unordered_set<std::string_view>& task_names,
    std::string_view func_name, DiagEngine& diag) {
  if (s->kind == StmtKind::kReturn && s->expr && is_void) {
    diag.Error(s->range.start, "void function returns a value");
  }
  if (s->kind == StmtKind::kFork && s->join_kind != TokenKind::kKwJoinNone) {
    diag.Error(s->range.start,
               "only fork/join_none is permitted inside a function");
  }

  if (s->kind == StmtKind::kDelay || s->kind == StmtKind::kCycleDelay ||
      s->kind == StmtKind::kEventControl ||
      s->kind == StmtKind::kTimingControl || s->kind == StmtKind::kWait ||
      s->kind == StmtKind::kWaitFork || s->kind == StmtKind::kWaitOrder ||
      s->kind == StmtKind::kExpect) {
    diag.Error(s->range.start,
               "time-controlling statement is not allowed inside a function");
  }

  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kCall &&
      task_names.count(s->expr->callee) != 0) {
    diag.Error(s->range.start, "function cannot enable a task");
  }

  if (s->kind == StmtKind::kVarDecl && !func_name.empty() &&
      s->var_name == func_name) {
    diag.Error(s->range.start,
               std::format("declaration of '{}' conflicts with function name",
                           func_name));
  }

  if (s->kind == StmtKind::kVarDecl && s->var_is_static && s->var_init) {
    if (!IsConstantExpr(s->var_init)) {
      diag.Error(s->range.start,
                 std::format("static variable '{}' initializer must be a "
                             "constant expression",
                             s->var_name));
    }
  }
  if (s->kind == StmtKind::kAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS");
  }

  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts) CheckNoReturnInFork(sub, diag);
  }
}

static void CheckFuncBodyStmt(
    const Stmt* s, bool is_void,
    const std::unordered_set<std::string_view>& task_names,
    std::string_view func_name, DiagEngine& diag) {
  if (!s) return;
  CheckFuncBodyStmtSelf(s, is_void, task_names, func_name, diag);

  if (s->kind == StmtKind::kFork && s->join_kind == TokenKind::kKwJoinNone)
    return;
  for (auto* sub : s->stmts)
    CheckFuncBodyStmt(sub, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->then_branch, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->else_branch, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->body, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->for_body, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->assert_pass_stmt, is_void, task_names, func_name, diag);
  CheckFuncBodyStmt(s->assert_fail_stmt, is_void, task_names, func_name, diag);
  for (auto& ci : s->case_items)
    CheckFuncBodyStmt(ci.body, is_void, task_names, func_name, diag);
  for (auto& ri : s->randcase_items)
    CheckFuncBodyStmt(ri.second, is_void, task_names, func_name, diag);
}

// §13.3.2: an automatic task variable is deallocated when the invocation ends,
// so a reference to one must not outlive the call. Walk an expression tree
// looking for any leaf identifier naming such a variable.
static bool ExprRefsAutoVar(
    const Expr* e, const std::unordered_set<std::string_view>& auto_vars);

static bool AnyChildExprRefsAutoVar(
    const Expr* e, const std::unordered_set<std::string_view>& auto_vars) {
  const Expr* const kChildren[] = {
      e->lhs,       e->rhs,       e->base,       e->index,     e->index_end,
      e->condition, e->true_expr, e->false_expr, e->with_expr, e->repeat_count};
  for (const Expr* child : kChildren)
    if (ExprRefsAutoVar(child, auto_vars)) return true;
  for (auto* a : e->args)
    if (ExprRefsAutoVar(a, auto_vars)) return true;
  for (auto* el : e->elements)
    if (ExprRefsAutoVar(el, auto_vars)) return true;
  return false;
}

static bool ExprRefsAutoVar(
    const Expr* e, const std::unordered_set<std::string_view>& auto_vars) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && !e->text.empty() &&
      auto_vars.count(e->text) != 0)
    return true;
  return AnyChildExprRefsAutoVar(e, auto_vars);
}

// §13.3.2: the nonblocking-assignment restriction applies to a write into an
// automatic task variable's own storage, including a bit-select or part-select
// of it. A bit/part-select chain is walked down to its root name. Member access
// is deliberately not traversed: it denotes a write through a handle or
// reference whose target outlives the automatic variable.
static std::string_view NbaAutoTargetRoot(const Expr* e) {
  while (e && e->kind == ExprKind::kSelect) e = e->base;
  if (e && e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

// §13.3.2: an automatic task variable shall not appear in the
// intra-assignment event control of a nonblocking assignment, since the
// event control can defer evaluation past the variable's lifetime.
static void CheckNbaEventControlForAutoVar(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    DiagEngine& diag) {
  bool in_event_control = ExprRefsAutoVar(s->repeat_event_count, auto_vars);
  for (const auto& ev : s->events) {
    if (ExprRefsAutoVar(ev.signal, auto_vars) ||
        ExprRefsAutoVar(ev.iff_condition, auto_vars)) {
      in_event_control = true;
    }
  }
  if (in_event_control) {
    diag.Error(s->range.start,
               "automatic task variable in intra-assignment event control "
               "of nonblocking assignment");
  }
}

static void CheckTaskBodyStmtSelf(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    DiagEngine& diag) {
  if (s->kind == StmtKind::kReturn && s->expr) {
    diag.Error(s->range.start, "task returns a value");
  }

  if (s->kind == StmtKind::kNonblockingAssign && s->lhs) {
    auto target = NbaAutoTargetRoot(s->lhs);
    if (!target.empty() && auto_vars.count(target) != 0) {
      diag.Error(s->range.start,
                 "automatic task variable in nonblocking assignment");
    }
  }

  if (s->kind == StmtKind::kNonblockingAssign) {
    CheckNbaEventControlForAutoVar(s, auto_vars, diag);
  }

  // §13.3.2: an automatic task variable shall not be traced by continuous
  // monitoring system tasks such as $monitor and $dumpvars, whose tracing
  // outlives the invocation.
  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kSystemCall &&
      (s->expr->callee == "$monitor" || s->expr->callee == "$dumpvars")) {
    for (auto* a : s->expr->args) {
      if (ExprRefsAutoVar(a, auto_vars)) {
        diag.Error(s->range.start,
                   "automatic task variable traced by system task");
        break;
      }
    }
  }

  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty() && auto_vars.count(name) != 0) {
      diag.Error(s->range.start,
                 "automatic variable in procedural continuous assignment");
    }
  }
  if (s->kind == StmtKind::kAssign && s->lhs &&
      s->lhs->kind == ExprKind::kSelect) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS");
  }

  if (s->kind == StmtKind::kFork) {
    for (auto* sub : s->fork_stmts) CheckNoReturnInFork(sub, diag);
  }
}

static void CheckTaskBodyStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    DiagEngine& diag) {
  if (!s) return;
  CheckTaskBodyStmtSelf(s, auto_vars, diag);
  for (auto* sub : s->stmts) CheckTaskBodyStmt(sub, auto_vars, diag);
  for (auto* sub : s->fork_stmts) CheckTaskBodyStmt(sub, auto_vars, diag);
  CheckTaskBodyStmt(s->then_branch, auto_vars, diag);
  CheckTaskBodyStmt(s->else_branch, auto_vars, diag);
  CheckTaskBodyStmt(s->body, auto_vars, diag);
  CheckTaskBodyStmt(s->for_body, auto_vars, diag);
  for (auto& ci : s->case_items) CheckTaskBodyStmt(ci.body, auto_vars, diag);
}

static void CollectAutoVarNames(const Stmt* s, bool task_is_auto,
                                std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    if (task_is_auto && !s->var_is_static) {
      out.insert(s->var_name);
    } else if (!task_is_auto && s->var_is_automatic) {
      out.insert(s->var_name);
    }
  }
  for (auto* sub : s->stmts) CollectAutoVarNames(sub, task_is_auto, out);
  CollectAutoVarNames(s->then_branch, task_is_auto, out);
  CollectAutoVarNames(s->else_branch, task_is_auto, out);
  CollectAutoVarNames(s->body, task_is_auto, out);
  CollectAutoVarNames(s->for_body, task_is_auto, out);
  for (auto& ci : s->case_items)
    CollectAutoVarNames(ci.body, task_is_auto, out);
}

static void ValidateFunctionArgDecls(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& class_names, DiagEngine& diag) {
  for (const auto& arg : item->func_args) {
    if (arg.data_type.kind == DataTypeKind::kNamed &&
        arg.data_type.type_name == "weak_reference" &&
        !arg.data_type.type_params.empty()) {
      const auto& tp = arg.data_type.type_params[0];
      if (tp.kind != DataTypeKind::kNamed || !class_names.count(tp.type_name)) {
        diag.Error(item->loc,
                   "weak_reference type parameter shall be a class type");
      }
    }
    if (arg.default_value && !item->is_ansi_ports) {
      diag.Error(item->loc,
                 std::format("default argument values are only allowed with "
                             "ANSI-style port declarations for '{}'",
                             arg.name));
    }
  }
}

static void ValidateRefArgsInForkBlocks(const ModuleItem* item,
                                        DiagEngine& diag) {
  std::unordered_set<std::string_view> ref_names;
  for (const auto& arg : item->func_args) {
    if (arg.direction == Direction::kRef && !arg.is_ref_static) {
      ref_names.insert(arg.name);
    }
  }
  if (!ref_names.empty()) {
    for (auto* s : item->func_body_stmts)
      CheckRefArgsInForkBlocks(s, ref_names, diag);
  }
}

static void ValidateTaskBody(const ModuleItem* item, DiagEngine& diag) {
  bool is_auto = item->is_automatic;

  std::unordered_set<std::string_view> auto_vars;
  if (is_auto) {
    for (const auto& arg : item->func_args) {
      auto_vars.insert(arg.name);
    }
  }
  for (auto* s : item->func_body_stmts) {
    CollectAutoVarNames(s, is_auto, auto_vars);
  }
  for (auto* s : item->func_body_stmts) {
    CheckTaskBodyStmt(s, auto_vars, diag);
  }
}

void Elaborator::ValidateFunctionBody(const ModuleItem* item) {
  ValidateRefLifetime(item, diag_);

  ValidateConstRefWriteProtection(item, diag_);

  ValidateFunctionArgDecls(item, class_names_, diag_);

  ValidateRefArgsInForkBlocks(item, diag_);

  if (item->kind == ModuleItemKind::kTaskDecl) {
    ValidateTaskBody(item, diag_);
    return;
  }
  if (item->kind != ModuleItemKind::kFunctionDecl) return;
  bool is_void = (item->return_type.kind == DataTypeKind::kVoid);
  for (auto* s : item->func_body_stmts) {
    CheckFuncBodyStmt(s, is_void, task_names_, item->name, diag_);
  }
}

namespace {

void CollectIdentLeaves(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  switch (e->kind) {
    case ExprKind::kIdentifier:
      if (!e->text.empty() && e->text.front() != '$') out.push_back(e);
      return;
    case ExprKind::kCall:
    case ExprKind::kSystemCall:
      for (auto* a : e->args) CollectIdentLeaves(a, out);
      return;
    case ExprKind::kMemberAccess:
      CollectIdentLeaves(e->lhs, out);
      return;
    case ExprKind::kTypeRef:
      return;
    default:
      break;
  }
  CollectIdentLeaves(e->lhs, out);
  CollectIdentLeaves(e->rhs, out);
  CollectIdentLeaves(e->base, out);
  CollectIdentLeaves(e->index, out);
  CollectIdentLeaves(e->index_end, out);
  CollectIdentLeaves(e->condition, out);
  CollectIdentLeaves(e->true_expr, out);
  CollectIdentLeaves(e->false_expr, out);
  CollectIdentLeaves(e->repeat_count, out);
  CollectIdentLeaves(e->with_expr, out);
  for (auto* a : e->args) CollectIdentLeaves(a, out);
  for (auto* el : e->elements) CollectIdentLeaves(el, out);
}

}  // namespace

void Elaborator::ValidateFunctionArgDefaultsScope(const ModuleItem* item) {
  if (!item) return;
  if (!item->is_ansi_ports) return;
  if (!item->method_class.empty()) return;
  std::unordered_set<std::string_view> prior_args;
  for (const auto& arg : item->func_args) {
    if (arg.default_value) {
      std::vector<const Expr*> idents;
      CollectIdentLeaves(arg.default_value, idents);
      for (const auto* e : idents) {
        auto name = e->text;
        if (name.empty()) continue;
        if (prior_args.count(name)) continue;
        if (IsNameInModuleScope(name)) continue;
        diag_.Error(e->range.start,
                    std::format("default value for '{}' references '{}' "
                                "which is not declared in the subroutine's "
                                "declaring scope",
                                arg.name, name));
      }
    }
    if (!arg.name.empty()) prior_args.insert(arg.name);
  }
}

static void CheckAutoVarWritesInProc(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kNonblockingAssign && s->lhs &&
      s->lhs->kind == ExprKind::kIdentifier &&
      auto_vars.count(s->lhs->text) != 0) {
    diag.Error(s->range.start, "automatic variable in nonblocking assignment");
  }
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kAssign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty() && auto_vars.count(name) != 0) {
      diag.Error(s->range.start,
                 "automatic variable in procedural continuous assignment");
    }
  }
  for (auto* sub : s->stmts) CheckAutoVarWritesInProc(sub, auto_vars, diag);
  for (auto* sub : s->fork_stmts)
    CheckAutoVarWritesInProc(sub, auto_vars, diag);
  CheckAutoVarWritesInProc(s->then_branch, auto_vars, diag);
  CheckAutoVarWritesInProc(s->else_branch, auto_vars, diag);
  CheckAutoVarWritesInProc(s->body, auto_vars, diag);
  CheckAutoVarWritesInProc(s->for_body, auto_vars, diag);
  for (auto& ci : s->case_items)
    CheckAutoVarWritesInProc(ci.body, auto_vars, diag);
}

void Elaborator::ValidateAutomaticVarProcWrites(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock ||
                   item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock;
    if (!is_proc || !item->body) continue;
    std::unordered_set<std::string_view> auto_vars;
    CollectAutoVarNames(item->body, false, auto_vars);
    if (auto_vars.empty()) continue;
    CheckAutoVarWritesInProc(item->body, auto_vars, diag_);
  }
}

}  // namespace delta
