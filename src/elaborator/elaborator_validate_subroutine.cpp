#include <format>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// §7.7: returns true when a positional DPI formal is an open-array (unsized)
// output formal that may not receive a dynamic array or queue actual.
static bool IsDpiOpenArrayOutputFormal(const FunctionArg& formal) {
  bool is_open =
      !formal.unpacked_dims.empty() && formal.unpacked_dims[0] == nullptr;
  bool is_output = formal.direction == Direction::kOutput ||
                   formal.direction == Direction::kInout;
  return is_open && is_output;
}

// §7.7: true when every name in `arg_names` is empty, i.e. the call uses pure
// positional binding (named association suppresses this analysis).
static bool AllPositionalArgs(const Expr* call) {
  for (auto name : call->arg_names) {
    if (!name.empty()) return false;
  }
  return true;
}

// §7.7: true when the i-th positional actual of `call` is an identifier naming
// a dynamic array or queue, given the per-variable array info map.
static bool ActualIsDynamicOrQueue(
    const Expr* actual,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info) {
  if (!actual || actual->kind != ExprKind::kIdentifier) return false;
  auto vit = var_array_info.find(actual->text);
  if (vit == var_array_info.end()) return false;
  return vit->second.is_dynamic || vit->second.is_queue;
}

// §7.7: at a DPI import call, an open-array (unsized) formal with an output
// direction may not receive a dynamic array or queue actual. The unsized
// dimension means the C side has no agreed-upon element count to write back
// into, so this association is prohibited.
void Elaborator::CheckDpiOpenArrayCall(const Expr* call) {
  if (!call || call->kind != ExprKind::kCall || call->callee.empty()) return;
  auto it = dpi_import_decls_.find(call->callee);
  if (it == dpi_import_decls_.end() || it->second == nullptr) return;
  const ModuleItem* imp = it->second;
  // Only positional binding is analyzed; named association is left untouched.
  if (!AllPositionalArgs(call)) return;
  size_t count = std::min(call->args.size(), imp->func_args.size());
  for (size_t i = 0; i < count; ++i) {
    if (!IsDpiOpenArrayOutputFormal(imp->func_args[i])) continue;
    const Expr* actual = call->args[i];
    if (!ActualIsDynamicOrQueue(actual, var_array_info_)) continue;
    diag_.Error(actual->range.start,
                std::format("a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import '{}'",
                            call->callee));
  }
}

void Elaborator::WalkExprForDpiCalls(const Expr* e) {
  if (!e) return;
  CheckDpiOpenArrayCall(e);
  WalkExprForDpiCalls(e->lhs);
  WalkExprForDpiCalls(e->rhs);
  WalkExprForDpiCalls(e->condition);
  WalkExprForDpiCalls(e->true_expr);
  WalkExprForDpiCalls(e->false_expr);
  WalkExprForDpiCalls(e->base);
  WalkExprForDpiCalls(e->index);
  WalkExprForDpiCalls(e->index_end);
  for (auto* a : e->args) WalkExprForDpiCalls(a);
  for (auto* el : e->elements) WalkExprForDpiCalls(el);
}

void Elaborator::WalkStmtsForDpiArgs(const Stmt* s) {
  if (!s) return;
  WalkExprForDpiCalls(s->rhs);
  WalkExprForDpiCalls(s->expr);
  WalkExprForDpiCalls(s->condition);
  for (auto* sub : s->stmts) WalkStmtsForDpiArgs(sub);
  WalkStmtsForDpiArgs(s->then_branch);
  WalkStmtsForDpiArgs(s->else_branch);
  WalkStmtsForDpiArgs(s->body);
  WalkStmtsForDpiArgs(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForDpiArgs(ci.body);
}

void Elaborator::ValidateDpiOpenArrayArgs(const ModuleDecl* decl) {
  dpi_import_decls_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kDpiImport && !item->name.empty())
      dpi_import_decls_[item->name] = item;
  }
  if (dpi_import_decls_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body) WalkStmtsForDpiArgs(item->body);
    for (auto* s : item->func_body_stmts) WalkStmtsForDpiArgs(s);
    WalkExprForDpiCalls(item->init_expr);
  }
}

// §13.4.4: true when this statement node itself (ignoring substatements) is a
// background-process-spawning construct.
static bool StmtNodeSpawnsBackgroundProcess(const Stmt* s) {
  if (s->kind == StmtKind::kNonblockingAssign) return true;
  if (s->kind == StmtKind::kEventTrigger) return true;
  if (s->kind == StmtKind::kNbEventTrigger) return true;
  if (s->kind == StmtKind::kFork && s->join_kind == TokenKind::kKwJoinNone) {
    return true;
  }
  return false;
}

static bool StmtSpawnsBackgroundProcess(const Stmt* s);

// §13.4.4: true when any statement in one of `s`'s child statement-list slots
// spawns a background process.
static bool ChildStmtListSpawnsBackgroundProcess(const Stmt* s) {
  for (auto* sub : s->stmts)
    if (StmtSpawnsBackgroundProcess(sub)) return true;
  for (auto* sub : s->fork_stmts)
    if (StmtSpawnsBackgroundProcess(sub)) return true;
  for (auto& ci : s->case_items)
    if (StmtSpawnsBackgroundProcess(ci.body)) return true;
  for (auto& ri : s->randcase_items)
    if (StmtSpawnsBackgroundProcess(ri.second)) return true;
  return false;
}

// §13.4.4: true when one of `s`'s single-statement child slots spawns a
// background process.
static bool ChildStmtSlotSpawnsBackgroundProcess(const Stmt* s) {
  return StmtSpawnsBackgroundProcess(s->then_branch) ||
         StmtSpawnsBackgroundProcess(s->else_branch) ||
         StmtSpawnsBackgroundProcess(s->body) ||
         StmtSpawnsBackgroundProcess(s->for_body) ||
         StmtSpawnsBackgroundProcess(s->assert_pass_stmt) ||
         StmtSpawnsBackgroundProcess(s->assert_fail_stmt);
}

// §13.4.4: true when any substatement of `s` spawns a background process.
static bool ChildStmtSpawnsBackgroundProcess(const Stmt* s) {
  return ChildStmtListSpawnsBackgroundProcess(s) ||
         ChildStmtSlotSpawnsBackgroundProcess(s);
}

// §13.4.4
static bool StmtSpawnsBackgroundProcess(const Stmt* s) {
  if (!s) return false;
  if (StmtNodeSpawnsBackgroundProcess(s)) return true;
  return ChildStmtSpawnsBackgroundProcess(s);
}

// §13.4.4
static bool FuncSpawnsBackgroundProcess(const ModuleItem* func) {
  if (!func) return false;
  for (const auto* s : func->func_body_stmts) {
    if (StmtSpawnsBackgroundProcess(s)) return true;
  }
  return false;
}

// §13.4.4
static void CheckBackgroundFuncCallInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    auto it = func_decls.find(expr->callee);
    if (it != func_decls.end() && FuncSpawnsBackgroundProcess(it->second)) {
      diag.Error(expr->range.start,
                 std::format(
                     "function '{}' schedules a background event and cannot be "
                     "called from a continuous assignment",
                     expr->callee));
    }
  }
  CheckBackgroundFuncCallInExpr(expr->lhs, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->rhs, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->condition, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->true_expr, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->false_expr, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->base, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->index, func_decls, diag);
  CheckBackgroundFuncCallInExpr(expr->index_end, func_decls, diag);
  for (auto* arg : expr->args)
    CheckBackgroundFuncCallInExpr(arg, func_decls, diag);
  for (auto* elem : expr->elements)
    CheckBackgroundFuncCallInExpr(elem, func_decls, diag);
}

void Elaborator::ValidateBackgroundFuncCallContext(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kContAssign) continue;
    CheckBackgroundFuncCallInExpr(item->assign_rhs, func_decls_, diag_);
  }
}

static bool IsValidOutputArg(const Expr* e) {
  if (!e) return false;
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kSelect ||
         e->kind == ExprKind::kMemberAccess;
}

static bool IsArgProvided(const Expr* expr, size_t i, std::string_view name,
                          size_t positional_count) {
  if (expr->arg_names.empty())
    return (i < expr->args.size()) && (expr->args[i] != nullptr);
  if (i < positional_count) return (expr->args[i] != nullptr);
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == name) return true;
  }
  return false;
}

static void CheckRequiredArgs(const Expr* expr, const ModuleItem* func,
                              size_t positional_count, DiagEngine& diag) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    bool provided =
        IsArgProvided(expr, i, func->func_args[i].name, positional_count);
    if (!provided && !func->func_args[i].default_value) {
      diag.Error(expr->range.start,
                 std::format("missing argument '{}' in call to '{}'",
                             func->func_args[i].name, func->name));
    }
  }
}

static void CheckNamedArgs(const Expr* expr, const ModuleItem* func,
                           DiagEngine& diag) {
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    bool found = false;
    for (size_t i = 0; i < func->func_args.size(); ++i) {
      if (func->func_args[i].name == expr->arg_names[j]) {
        found = true;
        break;
      }
    }
    if (!found) {
      diag.Error(expr->range.start,
                 std::format("no parameter '{}' in '{}'", expr->arg_names[j],
                             func->name));
    }
  }
}

static int ResolveCallArgIndex(const Expr* expr, size_t i,
                               std::string_view name, size_t positional_count) {
  if (expr->arg_names.empty()) {
    return (i < expr->args.size()) ? static_cast<int>(i) : -1;
  }
  if (i < positional_count) return static_cast<int>(i);
  for (size_t j = 0; j < expr->arg_names.size(); ++j) {
    if (expr->arg_names[j] == name) {
      return static_cast<int>(positional_count + j);
    }
  }
  return -1;
}

static void CheckOutputArgs(const Expr* expr, const ModuleItem* func,
                            size_t positional_count, DiagEngine& diag) {
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    auto dir = func->func_args[i].direction;
    if (dir != Direction::kOutput && dir != Direction::kInout) continue;
    int ai =
        ResolveCallArgIndex(expr, i, func->func_args[i].name, positional_count);
    if (ai < 0) continue;
    auto* arg = expr->args[static_cast<size_t>(ai)];
    if (arg && !IsValidOutputArg(arg)) {
      diag.Error(arg->range.start,
                 std::format("{} argument '{}' requires a variable",
                             dir == Direction::kOutput ? "output" : "inout",
                             func->func_args[i].name));
    }
  }
}

static std::string_view RefActualNetName(
    const Expr* e, const std::unordered_set<std::string_view>& nets) {
  if (!e || nets.empty()) return {};
  if (e->kind == ExprKind::kIdentifier) {
    return nets.count(e->text) ? e->text : std::string_view{};
  }
  if (e->kind == ExprKind::kSelect) {
    return RefActualNetName(e->base, nets);
  }
  return {};
}

static void CheckRefArgsNotNets(
    const Expr* expr, const ModuleItem* func, size_t positional_count,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (net_names.empty()) return;
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    if (func->func_args[i].direction != Direction::kRef) continue;
    int ai =
        ResolveCallArgIndex(expr, i, func->func_args[i].name, positional_count);
    if (ai < 0) continue;
    auto* arg = expr->args[static_cast<size_t>(ai)];
    auto net = RefActualNetName(arg, net_names);
    if (net.empty()) continue;
    diag.Error(arg->range.start,
               std::format("net '{}' cannot be passed by reference to "
                           "argument '{}' of '{}'",
                           net, func->func_args[i].name, func->name));
  }
}

static void CheckCallArgs(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (!expr || expr->kind != ExprKind::kCall || expr->callee.empty()) return;
  auto it = func_decls.find(expr->callee);
  if (it == func_decls.end()) return;
  const auto* func = it->second;
  size_t param_count = func->func_args.size();
  size_t positional_count = expr->args.size() - expr->arg_names.size();
  if (positional_count > param_count) {
    diag.Error(expr->range.start,
               std::format("too many arguments to '{}': expected {}, got {}",
                           func->name, param_count, positional_count));
    return;
  }
  CheckRequiredArgs(expr, func, positional_count, diag);
  CheckNamedArgs(expr, func, diag);
  CheckOutputArgs(expr, func, positional_count, diag);
  CheckRefArgsNotNets(expr, func, positional_count, net_names, diag);
}

static void CheckVoidCallInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    auto it = func_decls.find(expr->callee);
    if (it != func_decls.end() &&
        it->second->kind == ModuleItemKind::kFunctionDecl &&
        it->second->return_type.kind == DataTypeKind::kVoid) {
      diag.Error(expr->range.start,
                 std::format("void function '{}' used as expression operand",
                             expr->callee));
    }
  }
  CheckVoidCallInExpr(expr->lhs, func_decls, diag);
  CheckVoidCallInExpr(expr->rhs, func_decls, diag);
  CheckVoidCallInExpr(expr->condition, func_decls, diag);
  CheckVoidCallInExpr(expr->true_expr, func_decls, diag);
  CheckVoidCallInExpr(expr->false_expr, func_decls, diag);
  for (auto* a : expr->args) CheckVoidCallInExpr(a, func_decls, diag);
  for (auto* e : expr->elements) CheckVoidCallInExpr(e, func_decls, diag);
}

static std::string_view ForbiddenFuncArgInNonProc(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  if (!expr || expr->kind != ExprKind::kCall || expr->callee.empty()) return {};
  auto it = func_decls.find(expr->callee);
  if (it == func_decls.end()) return {};
  const auto* func = it->second;
  if (func->kind != ModuleItemKind::kFunctionDecl) return {};
  for (const auto& arg : func->func_args) {
    if (arg.direction == Direction::kOutput) return "output";
    if (arg.direction == Direction::kInout) return "inout";

    if (arg.direction == Direction::kRef && !arg.is_const) return "ref";
  }
  return {};
}

static void CheckNoTaskCallInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& decls,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    auto it = decls.find(expr->callee);
    if (it != decls.end() && it->second->kind == ModuleItemKind::kTaskDecl) {
      diag.Error(expr->range.start,
                 std::format("task '{}' cannot be called in an event "
                             "expression",
                             expr->callee));
    }
  }
  CheckNoTaskCallInExpr(expr->lhs, decls, diag);
  CheckNoTaskCallInExpr(expr->rhs, decls, diag);
  CheckNoTaskCallInExpr(expr->condition, decls, diag);
  CheckNoTaskCallInExpr(expr->true_expr, decls, diag);
  CheckNoTaskCallInExpr(expr->false_expr, decls, diag);
  CheckNoTaskCallInExpr(expr->base, decls, diag);
  CheckNoTaskCallInExpr(expr->index, decls, diag);
  CheckNoTaskCallInExpr(expr->index_end, decls, diag);
  for (auto* a : expr->args) CheckNoTaskCallInExpr(a, decls, diag);
  for (auto* e : expr->elements) CheckNoTaskCallInExpr(e, decls, diag);
}

static void CheckEventExprSingular(
    const Expr* expr,
    const std::unordered_set<std::string_view>& non_singular_vars,
    const std::unordered_set<std::string_view>& non_singular_funcs,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier && !expr->text.empty()) {
    if (non_singular_vars.count(expr->text) != 0) {
      diag.Error(expr->range.start,
                 std::format("event expression references non-singular "
                             "variable '{}'; event expressions shall return "
                             "singular values",
                             expr->text));
    }
  }
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    if (non_singular_funcs.count(expr->callee) != 0) {
      diag.Error(expr->range.start,
                 std::format("event expression calls function '{}' whose "
                             "return type is non-singular; event expressions "
                             "shall return singular values",
                             expr->callee));
    }
  }
  CheckEventExprSingular(expr->lhs, non_singular_vars, non_singular_funcs,
                         diag);
  CheckEventExprSingular(expr->rhs, non_singular_vars, non_singular_funcs,
                         diag);
  CheckEventExprSingular(expr->condition, non_singular_vars, non_singular_funcs,
                         diag);
  CheckEventExprSingular(expr->true_expr, non_singular_vars, non_singular_funcs,
                         diag);
  CheckEventExprSingular(expr->false_expr, non_singular_vars,
                         non_singular_funcs, diag);
  for (auto* a : expr->args)
    CheckEventExprSingular(a, non_singular_vars, non_singular_funcs, diag);
  for (auto* e : expr->elements)
    CheckEventExprSingular(e, non_singular_vars, non_singular_funcs, diag);
}

static void WalkStmtForEventSingular(
    const Stmt* s,
    const std::unordered_set<std::string_view>& non_singular_vars,
    const std::unordered_set<std::string_view>& non_singular_funcs,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kEventControl) {
    for (const auto& ev : s->events) {
      CheckEventExprSingular(ev.signal, non_singular_vars, non_singular_funcs,
                             diag);
      CheckEventExprSingular(ev.iff_condition, non_singular_vars,
                             non_singular_funcs, diag);
    }
  }
  for (auto* sub : s->stmts)
    WalkStmtForEventSingular(sub, non_singular_vars, non_singular_funcs, diag);
  WalkStmtForEventSingular(s->then_branch, non_singular_vars,
                           non_singular_funcs, diag);
  WalkStmtForEventSingular(s->else_branch, non_singular_vars,
                           non_singular_funcs, diag);
  WalkStmtForEventSingular(s->body, non_singular_vars, non_singular_funcs,
                           diag);
  for (auto* fi : s->for_inits)
    WalkStmtForEventSingular(fi, non_singular_vars, non_singular_funcs, diag);
  WalkStmtForEventSingular(s->for_body, non_singular_vars, non_singular_funcs,
                           diag);
  for (auto* fs : s->for_steps)
    WalkStmtForEventSingular(fs, non_singular_vars, non_singular_funcs, diag);
  for (auto& ci : s->case_items)
    WalkStmtForEventSingular(ci.body, non_singular_vars, non_singular_funcs,
                             diag);
}

static void CheckCallNoOutInoutRefInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag, std::string_view context) {
  if (!expr) return;
  auto bad = ForbiddenFuncArgInNonProc(expr, func_decls);
  if (!bad.empty()) {
    diag.Error(expr->range.start,
               std::format("function '{}' has {} argument; cannot be called "
                           "in {}",
                           expr->callee, bad, context));
  }
  CheckCallNoOutInoutRefInExpr(expr->lhs, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->rhs, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->condition, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->true_expr, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->false_expr, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->base, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->index, func_decls, diag, context);
  CheckCallNoOutInoutRefInExpr(expr->index_end, func_decls, diag, context);
  for (auto* a : expr->args)
    CheckCallNoOutInoutRefInExpr(a, func_decls, diag, context);
  for (auto* e : expr->elements)
    CheckCallNoOutInoutRefInExpr(e, func_decls, diag, context);
}

static void WalkExprForCallArgs(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (!expr) return;
  CheckCallArgs(expr, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->lhs, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->rhs, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->condition, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->true_expr, func_decls, net_names, diag);
  WalkExprForCallArgs(expr->false_expr, func_decls, net_names, diag);
  for (auto* a : expr->args)
    WalkExprForCallArgs(a, func_decls, net_names, diag);
  for (auto* e : expr->elements)
    WalkExprForCallArgs(e, func_decls, net_names, diag);
}

// §13.5.5: a bare-identifier expression statement that names a subroutine is a
// paren-omitted call; check that the omission is legal here.
static void CheckParenOmittedCall(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  auto it = func_decls.find(s->expr->text);
  if (it == func_decls.end()) return;
  const auto* func = it->second;
  bool is_task = func->kind == ModuleItemKind::kTaskDecl;
  bool is_void_func = func->kind == ModuleItemKind::kFunctionDecl &&
                      func->return_type.kind == DataTypeKind::kVoid;
  if (!is_task && !is_void_func) {
    diag.Error(s->expr->range.start,
               std::format("cannot omit parentheses in call to nonvoid "
                           "function '{}'",
                           s->expr->text));
    return;
  }
  // §13.5.5: parentheses may be omitted only when the subroutine has
  // no formal arguments, or when every formal has a default value.
  bool all_have_defaults = true;
  for (const auto& arg : func->func_args) {
    if (!arg.default_value) {
      all_have_defaults = false;
      break;
    }
  }
  if (!all_have_defaults) {
    diag.Error(s->expr->range.start,
               std::format("cannot omit parentheses in call to '{}': "
                           "not all formal arguments have defaults",
                           s->expr->text));
  }
}

// §13.4.1: an expression-statement call discards its result; warn if it is a
// nonvoid function (a void'(...) cast wraps the call in a kCast and so does not
// reach this check). Also checks the argument expressions for void operands.
static void CheckDiscardedCallStmt(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  for (auto* a : s->expr->args) CheckVoidCallInExpr(a, func_decls, diag);

  auto fit = func_decls.find(s->expr->callee);
  if (fit == func_decls.end()) return;
  const auto* func = fit->second;
  if (func->kind == ModuleItemKind::kFunctionDecl &&
      func->return_type.kind != DataTypeKind::kVoid) {
    diag.Warning(
        s->expr->range.start,
        std::format("return value of nonvoid function '{}' is discarded; "
                    "cast to void to silence this warning",
                    s->expr->callee));
  }
}

// §9.4.2: an event expression cannot call functions with out/inout/ref
// arguments, cannot call tasks, and must yield singular values.
static void CheckEventControlCalls(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  for (const auto& ev : s->events) {
    CheckCallNoOutInoutRefInExpr(ev.signal, func_decls, diag,
                                 "an event expression");
    CheckCallNoOutInoutRefInExpr(ev.iff_condition, func_decls, diag,
                                 "an event expression");

    CheckNoTaskCallInExpr(ev.signal, func_decls, diag);
    CheckNoTaskCallInExpr(ev.iff_condition, func_decls, diag);
  }
}

static void WalkStmtForCallArgs(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag);

// Recurse into every substatement / sub-expression of `s`.
static void WalkChildStmtsForCallArgs(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  WalkExprForCallArgs(s->expr, func_decls, net_names, diag);
  WalkExprForCallArgs(s->lhs, func_decls, net_names, diag);
  WalkExprForCallArgs(s->rhs, func_decls, net_names, diag);
  WalkExprForCallArgs(s->condition, func_decls, net_names, diag);
  for (auto* sub : s->stmts)
    WalkStmtForCallArgs(sub, func_decls, net_names, diag);
  WalkStmtForCallArgs(s->then_branch, func_decls, net_names, diag);
  WalkStmtForCallArgs(s->else_branch, func_decls, net_names, diag);
  WalkStmtForCallArgs(s->body, func_decls, net_names, diag);
  for (auto* fi : s->for_inits)
    WalkStmtForCallArgs(fi, func_decls, net_names, diag);
  WalkStmtForCallArgs(s->for_body, func_decls, net_names, diag);
  for (auto* fs : s->for_steps)
    WalkStmtForCallArgs(fs, func_decls, net_names, diag);
  WalkExprForCallArgs(s->for_cond, func_decls, net_names, diag);
  for (auto& ci : s->case_items)
    WalkStmtForCallArgs(ci.body, func_decls, net_names, diag);
}

static void WalkStmtForCallArgs(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  if (!s) return;

  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kIdentifier) {
    CheckParenOmittedCall(s, func_decls, diag);
  }

  if (s->kind == StmtKind::kExprStmt && s->expr &&
      s->expr->kind == ExprKind::kCall) {
    CheckDiscardedCallStmt(s, func_decls, diag);
  } else {
    CheckVoidCallInExpr(s->expr, func_decls, diag);
  }
  CheckVoidCallInExpr(s->rhs, func_decls, diag);
  CheckVoidCallInExpr(s->condition, func_decls, diag);
  CheckVoidCallInExpr(s->for_cond, func_decls, diag);

  if (s->kind == StmtKind::kAssign || s->kind == StmtKind::kForce) {
    CheckCallNoOutInoutRefInExpr(s->rhs, func_decls, diag,
                                 "a procedural continuous assignment");
  }
  if (s->kind == StmtKind::kEventControl) {
    CheckEventControlCalls(s, func_decls, diag);
  }
  WalkChildStmtsForCallArgs(s, func_decls, net_names, diag);
}

// A scope randomize is a randomize_call that is not a method on a class
// object — see §A.8.2's randomize_call production and its footnote 43. The
// parser leaves `randomize` as a plain identifier, so we detect the scope
// form syntactically: either a bare callee with no member-access prefix, or
// a callee reached through the `std::` package scope. The kCall's `callee`
// field carries the simple-identifier text only, so we inspect `lhs` to
// distinguish the bare and `std::` forms from a class-method `obj.randomize`.
static bool IsScopeRandomizeCall(const Expr* expr) {
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

// Footnote 43 (§A.8.2): in a scope randomize_call, `null` is not a legal
// argument and the with-clause's parenthesized identifier_list is also
// illegal. Walks the expression tree and reports each offending site. The
// parenthesized-form check uses the `with_has_parens` AST flag set by the
// parser regardless of whether the parenthesized list happened to be empty
// or non-empty.
static void CheckScopeRandomizeRulesInExpr(const Expr* expr, DiagEngine& diag) {
  if (!expr) return;
  if (IsScopeRandomizeCall(expr)) {
    for (const auto* arg : expr->args) {
      if (arg && arg->kind == ExprKind::kIdentifier && arg->text == "null") {
        diag.Error(arg->range.start,
                   "'null' is not a legal argument to a scope randomize call");
      }
    }
    if (expr->with_has_parens) {
      diag.Error(expr->range.start,
                 "scope randomize call cannot use a parenthesized identifier "
                 "list after 'with'");
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

static void WalkStmtForScopeRandomize(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  CheckScopeRandomizeRulesInExpr(s->expr, diag);
  CheckScopeRandomizeRulesInExpr(s->lhs, diag);
  CheckScopeRandomizeRulesInExpr(s->rhs, diag);
  CheckScopeRandomizeRulesInExpr(s->condition, diag);
  CheckScopeRandomizeRulesInExpr(s->for_cond, diag);
  for (const auto* sub : s->stmts) WalkStmtForScopeRandomize(sub, diag);
  WalkStmtForScopeRandomize(s->then_branch, diag);
  WalkStmtForScopeRandomize(s->else_branch, diag);
  WalkStmtForScopeRandomize(s->body, diag);
  for (const auto* fi : s->for_inits) WalkStmtForScopeRandomize(fi, diag);
  WalkStmtForScopeRandomize(s->for_body, diag);
  for (const auto* fs : s->for_steps) WalkStmtForScopeRandomize(fs, diag);
  for (const auto& ci : s->case_items) WalkStmtForScopeRandomize(ci.body, diag);
}

static bool IsProceduralBlock(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kInitialBlock ||
         item->kind == ModuleItemKind::kAlwaysBlock ||
         item->kind == ModuleItemKind::kAlwaysCombBlock ||
         item->kind == ModuleItemKind::kAlwaysFFBlock ||
         item->kind == ModuleItemKind::kAlwaysLatchBlock ||
         item->kind == ModuleItemKind::kFinalBlock;
}

// Builds a name→decl map of all callable subroutines (the elaborator's known
// functions plus the task declarations local to `decl`).
static std::unordered_map<std::string_view, const ModuleItem*> BuildAllDecls(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  std::unordered_map<std::string_view, const ModuleItem*> all_decls =
      func_decls;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) all_decls[item->name] = item;
  }
  return all_decls;
}

// Footnote 43 (§A.8.2): walk every procedural and subroutine body for illegal
// scope randomize_call forms.
static void ValidateScopeRandomizeInDecl(const ModuleDecl* decl,
                                         DiagEngine& diag) {
  for (const auto* item : decl->items) {
    if (IsProceduralBlock(item)) WalkStmtForScopeRandomize(item->body, diag);
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (const auto* s : item->func_body_stmts)
        WalkStmtForScopeRandomize(s, diag);
    }
  }
}

// Collects names of variables whose declared type is non-singular (an unpacked
// array or unpacked struct/union).
static std::unordered_set<std::string_view> CollectNonSingularVars(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> non_singular_vars;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    bool unpacked_array = !item->unpacked_dims.empty();
    bool unpacked_aggregate = (item->data_type.kind == DataTypeKind::kStruct ||
                               item->data_type.kind == DataTypeKind::kUnion) &&
                              !item->data_type.is_packed;
    if (unpacked_array || unpacked_aggregate)
      non_singular_vars.insert(item->name);
  }
  return non_singular_vars;
}

// Collects names of functions whose return type is non-singular (an unpacked
// struct/union), drawn from `decl` and the elaborator's known functions.
static std::unordered_set<std::string_view> CollectNonSingularFuncs(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  std::unordered_set<std::string_view> non_singular_funcs;
  auto add_if_non_singular_return = [&](const ModuleItem* item) {
    if (item->kind != ModuleItemKind::kFunctionDecl) return;
    const auto& rt = item->return_type;
    bool unpacked_aggregate =
        (rt.kind == DataTypeKind::kStruct || rt.kind == DataTypeKind::kUnion) &&
        !rt.is_packed;
    if (unpacked_aggregate) non_singular_funcs.insert(item->name);
  };
  for (const auto* item : decl->items) add_if_non_singular_return(item);
  for (const auto& [name, item] : func_decls) add_if_non_singular_return(item);
  return non_singular_funcs;
}

// Validates one sensitivity-list event expression (the `signal` and
// `iff_condition` of a single entry): call legality, no task calls, and
// singular-value requirements.
static void ValidateSensitivityEntry(
    const Expr* signal, const Expr* iff_condition,
    const std::unordered_map<std::string_view, const ModuleItem*>& all_decls,
    const std::unordered_set<std::string_view>& non_singular_vars,
    const std::unordered_set<std::string_view>& non_singular_funcs,
    DiagEngine& diag) {
  CheckCallNoOutInoutRefInExpr(signal, all_decls, diag, "an event expression");
  CheckCallNoOutInoutRefInExpr(iff_condition, all_decls, diag,
                               "an event expression");

  CheckNoTaskCallInExpr(signal, all_decls, diag);
  CheckNoTaskCallInExpr(iff_condition, all_decls, diag);

  CheckEventExprSingular(signal, non_singular_vars, non_singular_funcs, diag);
  CheckEventExprSingular(iff_condition, non_singular_vars, non_singular_funcs,
                         diag);
}

// Validates the event expressions in a procedural block's body and sensitivity
// list: call legality, no task calls, and singular-value requirements.
static void ValidateProcBlockEvents(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, const ModuleItem*>& all_decls,
    const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& non_singular_vars,
    const std::unordered_set<std::string_view>& non_singular_funcs,
    DiagEngine& diag) {
  WalkStmtForCallArgs(item->body, all_decls, net_names, diag);

  WalkStmtForEventSingular(item->body, non_singular_vars, non_singular_funcs,
                           diag);

  for (const auto& ev : item->sensitivity) {
    ValidateSensitivityEntry(ev.signal, ev.iff_condition, all_decls,
                             non_singular_vars, non_singular_funcs, diag);
  }
}

// Validates the subroutine-call rules in a function or task body.
static void ValidateSubroutineBodyCallArgs(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, const ModuleItem*>& all_decls,
    const std::unordered_set<std::string_view>& net_names, DiagEngine& diag) {
  for (auto* s : item->func_body_stmts) {
    WalkStmtForCallArgs(s, all_decls, net_names, diag);
  }
}

// Validates the subroutine-call rules in a continuous assignment's RHS.
static void ValidateContAssignCallArgs(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, const ModuleItem*>& all_decls,
    DiagEngine& diag) {
  CheckVoidCallInExpr(item->assign_rhs, all_decls, diag);

  CheckCallNoOutInoutRefInExpr(item->assign_rhs, all_decls, diag,
                               "a continuous assignment");
}

// Validates the subroutine-call rules in one top-level item.
static void ValidateCallArgsInItem(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, const ModuleItem*>& all_decls,
    const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& non_singular_vars,
    const std::unordered_set<std::string_view>& non_singular_funcs,
    DiagEngine& diag) {
  if (IsProceduralBlock(item)) {
    ValidateProcBlockEvents(item, all_decls, net_names, non_singular_vars,
                            non_singular_funcs, diag);
  }

  if (item->kind == ModuleItemKind::kFunctionDecl ||
      item->kind == ModuleItemKind::kTaskDecl) {
    ValidateSubroutineBodyCallArgs(item, all_decls, net_names, diag);
  }
  if (item->kind == ModuleItemKind::kContAssign) {
    ValidateContAssignCallArgs(item, all_decls, diag);
  }
}

void Elaborator::ValidateSubroutineCallArgs(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, const ModuleItem*> all_decls =
      BuildAllDecls(decl, func_decls_);

  ValidateScopeRandomizeInDecl(decl, diag_);

  std::unordered_set<std::string_view> non_singular_vars =
      CollectNonSingularVars(decl);
  std::unordered_set<std::string_view> non_singular_funcs =
      CollectNonSingularFuncs(decl, func_decls_);

  for (const auto* item : decl->items) {
    ValidateCallArgsInItem(item, all_decls, net_names_, non_singular_vars,
                           non_singular_funcs, diag_);
  }
}

}  // namespace delta
