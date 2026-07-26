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
                     "called outside an initial/always procedure or fork block",
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
    // §13.4.4: spawning a background event is a side effect that is only
    // permitted when the calling thread is created by an initial/always
    // procedure or a fork block. A continuous assignment is one such
    // disallowed context; so is the initialization of a declaration, which
    // happens at time zero outside any such procedure. The LRM's own illegal
    // example is a variable initializer (`bit y = watch_for_zero(stack);`).
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckBackgroundFuncCallInExpr(item->assign_rhs, func_decls_, diag_);
    } else if (item->kind == ModuleItemKind::kVarDecl ||
               item->kind == ModuleItemKind::kNetDecl) {
      CheckBackgroundFuncCallInExpr(item->init_expr, func_decls_, diag_);
    }
  }
}

}  // namespace delta
