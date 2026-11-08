#include <cstddef>
#include <format>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsDpiOpenArrayOutputFormal(const FunctionArg& formal) {
  bool is_open =
      !formal.unpacked_dims.empty() && formal.unpacked_dims[0] == nullptr;
  bool is_output = formal.direction == Direction::kOutput ||
                   formal.direction == Direction::kInout;
  return is_open && is_output;
}

static bool ActualIsDynamicOrQueue(
    const Expr* actual,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info) {
  if (!actual || actual->kind != ExprKind::kIdentifier) return false;
  auto vit = var_array_info.find(actual->text);
  if (vit == var_array_info.end()) return false;
  return vit->second.is_dynamic || vit->second.is_queue;
}

void Elaborator::CheckDpiOpenArrayCall(const Expr* call) {
  if (!call || call->kind != ExprKind::kCall || call->callee.empty()) return;
  auto it = dpi_import_decls_.find(call->callee);
  if (it == dpi_import_decls_.end() || it->second == nullptr) return;
  const ModuleItem* imp = it->second;
  size_t positional_count = call->args.size() - call->arg_names.size();
  for (size_t i = 0; i < imp->func_args.size(); ++i) {
    const FunctionArg& formal = imp->func_args[i];
    if (!IsDpiOpenArrayOutputFormal(formal)) continue;
    int at = ResolveActualArgIndex(call, i, formal.name, positional_count);
    if (at < 0) continue;
    const Expr* actual = call->args[static_cast<size_t>(at)];
    if (!ActualIsDynamicOrQueue(actual, var_array_info_)) continue;
    diag_.Error(actual->range.start,
                std::format("a dynamic array or queue cannot be passed to the "
                            "open-array output argument of DPI import '{}'",
                            call->callee),
                Subclause("7.7"));
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
  ForEachChildExpr(s, [this](Expr* const& e) { WalkExprForDpiCalls(e); });
  ForEachChildStmt(s, [this](Stmt* const& sub) { WalkStmtsForDpiArgs(sub); });
}

namespace {

struct TaskOperandCheck {
  std::unordered_set<std::string> tasks;
  DiagEngine& diag;
};

void WalkExprForTaskOperands(const Expr* e, const Expr* root,
                             const TaskOperandCheck& chk) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCall && e != root) {
    std::string name = CallName(e);
    if (chk.tasks.contains(name)) {
      chk.diag.Error(e->range.start,
                     std::format("task '{}' is enabled from a statement and "
                                 "cannot be an operand of an expression",
                                 name),
                     Subclause("13.3"));
    }
  }
  for (const Expr* sub : {e->lhs, e->rhs, e->condition, e->true_expr,
                          e->false_expr, e->base, e->index, e->index_end}) {
    WalkExprForTaskOperands(sub, root, chk);
  }
  for (auto* a : e->args) WalkExprForTaskOperands(a, root, chk);
  for (auto* el : e->elements) WalkExprForTaskOperands(el, root, chk);
}

void WalkStmtsForTaskOperands(const Stmt* s, const TaskOperandCheck& chk) {
  if (!s) return;
  const Expr* root = s->kind == StmtKind::kExprStmt ? s->expr : nullptr;
  ForEachChildExpr(
      s, [&](Expr* const& e) { WalkExprForTaskOperands(e, root, chk); });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForTaskOperands(sub, chk); });
}

void WalkItemsForTaskOperands(const std::vector<ModuleItem*>& items,
                              const TaskOperandCheck& chk);

void WalkGenerateForTaskOperands(const ModuleItem* item,
                                 const TaskOperandCheck& chk) {
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      WalkItemsForTaskOperands(item->gen_body, chk);
      if (item->gen_else) WalkGenerateForTaskOperands(item->gen_else, chk);
      break;
    case ModuleItemKind::kGenerateFor:
      WalkItemsForTaskOperands(item->gen_body, chk);
      break;
    case ModuleItemKind::kGenerateCase:
      for (const auto& ci : item->gen_case_items)
        WalkItemsForTaskOperands(ci.body, chk);
      break;
    default:
      break;
  }
}

void WalkItemsForTaskOperands(const std::vector<ModuleItem*>& items,
                              const TaskOperandCheck& chk) {
  for (const ModuleItem* item : items) {
    WalkStmtsForTaskOperands(item->body, chk);
    for (const Stmt* s : item->func_body_stmts)
      WalkStmtsForTaskOperands(s, chk);
    WalkExprForTaskOperands(item->assign_rhs, nullptr, chk);
    WalkExprForTaskOperands(item->init_expr, nullptr, chk);
    WalkGenerateForTaskOperands(item, chk);
  }
}

void AddUnitAndPackageTasks(
    const CompilationUnit& unit,
    const std::unordered_map<std::string_view, const ModuleItem*>& funcs,
    std::unordered_set<std::string>& tasks) {
  for (const ModuleItem* item : unit.cu_items) {
    if (item->kind == ModuleItemKind::kTaskDecl && item->method_class.empty() &&
        !funcs.contains(item->name))
      tasks.emplace(item->name);
  }
  for (const PackageDecl* pkg : unit.packages) {
    for (const ModuleItem* item : pkg->items) {
      if (item->kind == ModuleItemKind::kTaskDecl && item->method_class.empty())
        tasks.emplace(std::string(pkg->name) + "::" + std::string(item->name));
    }
  }
}

}  // namespace

std::string CallName(const Expr* call) {
  if (!call->callee.empty()) return std::string(call->callee);
  const Expr* scoped = call->lhs;
  if (scoped == nullptr || !scoped->is_scope_resolution) return {};
  return std::string(scoped->lhs->text) + "::" + std::string(scoped->rhs->text);
}

std::string EnabledSubroutineName(const Stmt* s) {
  if (const Expr* call = SubroutineCallOfStmt(s)) return CallName(call);
  if (s->kind == StmtKind::kExprStmt && s->expr != nullptr &&
      s->expr->kind == ExprKind::kIdentifier)
    return std::string(s->expr->text);
  return {};
}

std::unordered_set<std::string> Elaborator::ReachableTaskNames() const {
  std::unordered_set<std::string> tasks;
  for (std::string_view name : task_names_) tasks.emplace(name);
  if (unit_ != nullptr) AddUnitAndPackageTasks(*unit_, func_decls_, tasks);
  return tasks;
}

void Elaborator::ValidateTaskCallsInExpressions(const ModuleDecl* decl) {
  TaskOperandCheck chk{ReachableTaskNames(), diag_};
  if (chk.tasks.empty()) return;
  WalkItemsForTaskOperands(decl->items, chk);
}

static void CheckFinalTaskEnables(
    const Stmt* s, const std::unordered_set<std::string>& task_names,
    DiagEngine& diag) {
  if (!s) return;
  std::string name = EnabledSubroutineName(s);
  if (task_names.contains(name)) {
    diag.Error(s->range.start,
               std::format("final procedure enables task '{}'", name),
               Subclause("9.2.3"));
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckFinalTaskEnables(sub, task_names, diag);
  });
}

void Elaborator::ValidateFinalTaskEnables(const ModuleDecl* decl) {
  const std::unordered_set<std::string> kTasks = ReachableTaskNames();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) {
      CheckFinalTaskEnables(item->body, kTasks, diag_);
    }
  }
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

static bool ChildStmtSpawnsBackgroundProcess(const Stmt* s) {
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtSpawnsBackgroundProcess(sub);
  });
  return found;
}

static bool StmtSpawnsBackgroundProcess(const Stmt* s) {
  if (!s) return false;
  if (StmtNodeSpawnsBackgroundProcess(s)) return true;
  return ChildStmtSpawnsBackgroundProcess(s);
}

static bool FuncSpawnsBackgroundProcess(const ModuleItem* func) {
  if (!func) return false;
  for (const auto* s : func->func_body_stmts) {
    if (StmtSpawnsBackgroundProcess(s)) return true;
  }
  return false;
}

static void CollectExprCallees(const Expr* e,
                               std::vector<std::string_view>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCall) out.push_back(e->callee);
  ForEachExprChild(e,
                   [&](const Expr* child) { CollectExprCallees(child, out); });
}

static void CollectStmtCallees(const Stmt* s,
                               std::vector<std::string_view>& out) {
  if (s == nullptr) return;
  ForEachChildExpr(s, [&](Expr* const& e) { CollectExprCallees(e, out); });
  ForEachChildStmt(s, [&](Stmt* const& sub) { CollectStmtCallees(sub, out); });
}

static bool FuncReachesBackgroundProcess(
    const ModuleItem* func,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    std::unordered_set<const ModuleItem*>& visited) {
  if (func == nullptr || !visited.insert(func).second) return false;
  if (FuncSpawnsBackgroundProcess(func)) return true;
  std::vector<std::string_view> callees;
  for (const Stmt* s : func->func_body_stmts) CollectStmtCallees(s, callees);
  for (std::string_view name : callees) {
    auto it = func_decls.find(name);
    if (it != func_decls.end() &&
        FuncReachesBackgroundProcess(it->second, func_decls, visited))
      return true;
  }
  return false;
}

static void CheckBackgroundFuncCallInExpr(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty()) {
    auto it = func_decls.find(expr->callee);
    std::unordered_set<const ModuleItem*> visited;
    if (it != func_decls.end() &&
        FuncReachesBackgroundProcess(it->second, func_decls, visited)) {
      diag.Error(expr->range.start,
                 std::format(
                     "function '{}' schedules a background event and cannot be "
                     "called outside an initial/always procedure or fork block",
                     expr->callee),
                 Subclause("13.4.4"));
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
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckBackgroundFuncCallInExpr(item->assign_rhs, func_decls_, diag_);
    } else if (item->kind == ModuleItemKind::kVarDecl ||
               item->kind == ModuleItemKind::kNetDecl) {
      CheckBackgroundFuncCallInExpr(item->init_expr, func_decls_, diag_);
    }
  }
}

}  // namespace delta
