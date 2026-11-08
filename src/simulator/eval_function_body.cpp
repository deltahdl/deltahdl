#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_function_body_internal.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_instance_task.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/pattern_match.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/statement_coverage.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach.h"
#include "simulator/vpi_globals.h"

namespace delta {

static FuncFlow ExecFuncBlock(const Stmt* stmt, const FuncExecCtx& exec);

static const Stmt* FuncFindFinalElse(const Stmt* stmt) {
  const Stmt* cur = stmt;
  while (cur->else_branch && cur->else_branch->kind == StmtKind::kIf) {
    cur = cur->else_branch;
  }
  return cur->else_branch;
}

static FuncFlow ExecFuncUniqueIfBranch(const Stmt* stmt, UniqueIfChain& scan,
                                       CaseQualifier qual,
                                       const FuncExecCtx& exec) {
  if (scan.first_match) {
    if (scan.scoped) exec.ctx.RestoreScope(std::move(scan.bound));
    FuncFlow r = ExecFuncStmt(scan.first_match->then_branch, exec);
    if (scan.scoped) exec.ctx.PopScope();
    return r;
  }
  if (scan.has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else) return ExecFuncStmt(final_else, exec);
  } else if (qual == CaseQualifier::kUnique) {
    exec.ctx.AddPendingViolation(stmt->range.start,
                                 "unique if: no condition matched",
                                 Subclause("12.4.2.1"), qual);
  }
  return FuncFlow::kNext;
}

static FuncFlow ExecFuncUniqueIf(const Stmt* stmt, CaseQualifier qual,
                                 const FuncExecCtx& exec) {
  UniqueIfChain scan = EvalUniqueIfChain(stmt, exec.ctx, exec.arena);
  if (scan.match_count > 1) {
    exec.ctx.AddPendingViolation(stmt->range.start,
                                 "unique if: multiple conditions matched",
                                 Subclause("12.4.2.1"), qual);
  }
  return ExecFuncUniqueIfBranch(stmt, scan, qual, exec);
}

static FuncFlow ExecFuncPriorityIf(const Stmt* stmt, const FuncExecCtx& exec) {
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    bool scoped = false;
    if (EnterIfPredicate(cur->condition, exec.ctx, exec.arena, scoped)) {
      FuncFlow r = ExecFuncStmt(cur->then_branch, exec);
      if (scoped) exec.ctx.PopScope();
      return r;
    }
    if (scoped) exec.ctx.PopScope();
  }
  if (const Stmt* final_else = FuncFindFinalElse(stmt)) {
    return ExecFuncStmt(final_else, exec);
  }
  exec.ctx.AddPendingViolation(stmt->range.start,
                               "priority if: no condition matched",
                               Subclause("12.4.2.1"), CaseQualifier::kPriority);
  return FuncFlow::kNext;
}

static FuncFlow ExecFuncPlainIf(const Stmt* stmt, const FuncExecCtx& exec) {
  bool scoped = PatternBindsIdentifiers(stmt->condition);
  if (scoped) exec.ctx.PushScope();
  bool holds = scoped
                   ? EvalMatchesPredicate(stmt->condition, exec.ctx, exec.arena)
                   : EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy();
  FuncFlow r = holds ? ExecFuncStmt(stmt->then_branch, exec) : FuncFlow::kNext;
  if (scoped) exec.ctx.PopScope();
  if (!holds && stmt->else_branch) r = ExecFuncStmt(stmt->else_branch, exec);
  return r;
}

static FuncFlow ExecFuncIf(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  auto qual = stmt->qualifier;
  FuncFlow r =
      (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0)
          ? ExecFuncUniqueIf(stmt, qual, exec)
      : qual == CaseQualifier::kPriority ? ExecFuncPriorityIf(stmt, exec)
                                         : ExecFuncPlainIf(stmt, exec);
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return r;
}

static FuncFlow ExecFuncBlock(const Stmt* stmt, const FuncExecCtx& exec) {
  bool named = !stmt->label.empty();
  bool scoped = !named && BlockDeclaresLet(stmt);
  if (named) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  if (scoped) exec.ctx.PushScope();
  FuncNamedScope scope(stmt->label, exec);
  FuncFlow flow = FuncFlow::kNext;
  for (auto* c : stmt->stmts) {
    flow = ExecFuncStmt(c, exec);
    if (flow != FuncFlow::kNext) break;
  }
  if (named) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  if (scoped) exec.ctx.PopScope();
  return scope.Leave(flow);
}

static FuncFlow ExecFuncDisable(const Stmt* stmt, const FuncExecCtx& exec) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier) {
    return FuncFlow::kNext;
  }
  std::string_view target = stmt->expr->text;
  const auto& scopes = *exec.named_scopes;
  if (std::find(scopes.begin(), scopes.end(), target) == scopes.end()) {
    return FuncFlow::kNext;
  }
  GetGlobalVpiContext().NoteDisabled(stmt, exec.ctx.ActiveInstancePrefix());
  exec.ctx.SetDisableTarget(target);
  return FuncFlow::kDisable;
}

static bool ForInitNeedsScope(const Stmt* stmt) {
  for (const auto& t : stmt->for_init_types) {
    if (t.kind != DataTypeKind::kImplicit) return true;
  }
  return false;
}

static void ExecFuncForInits(const Stmt* stmt, const FuncExecCtx& exec) {
  for (size_t i = 0; i < stmt->for_inits.size(); ++i) {
    auto* init = stmt->for_inits[i];
    if (i < stmt->for_init_types.size() &&
        stmt->for_init_types[i].kind != DataTypeKind::kImplicit && init &&
        init->lhs && init->lhs->kind == ExprKind::kIdentifier) {
      CreateFuncLocalVar(init->lhs->text, stmt->for_init_types[i], init->rhs,
                         exec.ctx, exec.arena);
    } else if (init) {
      ExecFuncStmt(init, exec);
    }
  }
}

static FuncFlow ExecFuncForLoop(const Stmt* stmt, const FuncExecCtx& exec) {
  FuncFlow flow = FuncFlow::kNext;
  while (!stmt->for_cond ||
         EvalExpr(stmt->for_cond, exec.ctx, exec.arena).IsTruthy()) {
    flow = ExecFuncStmt(stmt->for_body, exec);
    if (!LoopGoesOn(flow)) break;
    for (auto* step : stmt->for_steps) ExecFuncStmt(step, exec);
  }
  return LoopExitFlow(flow);
}

static FuncFlow ExecFuncFor(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  FuncNamedScope named(stmt->label, exec);
  bool scoped = ForInitNeedsScope(stmt);
  if (scoped) exec.ctx.PushScope();
  ExecFuncForInits(stmt, exec);
  FuncFlow flow = ExecFuncForLoop(stmt, exec);
  if (scoped) exec.ctx.PopScope();
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return named.Leave(flow);
}

static FuncFlow ExecFuncWhile(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  FuncNamedScope named(stmt->label, exec);
  FuncFlow flow = FuncFlow::kNext;
  while (stmt->condition &&
         EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy()) {
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  }
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return named.Leave(LoopExitFlow(flow));
}

static FuncFlow ExecFuncDoWhile(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  FuncNamedScope named(stmt->label, exec);
  FuncFlow flow = FuncFlow::kNext;
  do {
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  } while (stmt->condition &&
           EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy());
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return named.Leave(LoopExitFlow(flow));
}

static FuncFlow ExecFuncRepeatOrForever(const Stmt* stmt,
                                        const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  FuncNamedScope named(stmt->label, exec);
  std::optional<uint64_t> limit =
      LoopIterationLimit(stmt, exec.ctx, exec.arena);
  FuncFlow flow = FuncFlow::kNext;
  for (uint64_t i = 0; !limit || i < *limit; ++i) {
    flow = ExecFuncStmt(stmt->body, exec);
    if (!LoopGoesOn(flow)) break;
  }
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return named.Leave(LoopExitFlow(flow));
}

static void AssignArrayReturn(const Stmt* stmt, const FuncExecCtx& exec) {
  Expr name;
  name.kind = ExprKind::kIdentifier;
  name.text = exec.func_name;
  name.range = stmt->range;
  Stmt assign;
  assign.kind = StmtKind::kBlockingAssign;
  assign.lhs = &name;
  assign.rhs = stmt->expr;
  assign.range = stmt->range;
  ExecFuncBlockingAssign(&assign, exec.ctx, exec.arena);
}

static void ExecFuncReturn(const Stmt* stmt, const FuncExecCtx& exec) {
  if (exec.array_return) {
    AssignArrayReturn(stmt, exec);
    return;
  }
  if (TryFuncReturnClassNew(stmt->expr, exec.func_name, exec.ctx, exec.arena))
    return;
  Logic4Vec val = OwnRhsWords(
      EvalExpr(stmt->expr, exec.ctx, exec.arena, exec.ret_var->value.width),
      exec.arena);
  RecordReturnedAggregate(stmt->expr, exec.ctx, exec.arena);
  RecordReturnedTag(stmt->expr);
  RecordReturnedVariableTag(stmt->expr, exec.ctx);
  if (exec.ret_width != 0) {
    val = ConvertRealForKnownLhs(val, exec.ret_var->is_real, exec.ret_width,
                                 exec.arena);
    val.is_signed = exec.ret_var->is_signed;
  }
  exec.ret_var->value = val;
  if (!exec.ret_var->is_4state) CoerceTo2State(exec.ret_var->value);
}

static FuncFlow ExecFuncImmediateAssert(const Stmt* stmt,
                                        const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushActiveNamedScope(stmt->label);
  const Stmt* action =
      ExecImmediateAssertInFunction(stmt, exec.ctx, exec.arena);
  FuncFlow flow = ExecFuncStmt(action, exec);
  if (labeled) exec.ctx.PopActiveNamedScope();
  return flow;
}

static FuncFlow ExecFuncCase(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(exec.ctx.StmtFrameName(stmt));
  CaseSelection chosen = SelectCaseItem(stmt, exec.ctx, exec.arena);
  bool scoped = !chosen.bindings.empty();
  if (scoped) {
    exec.ctx.PushScope();
    InstallPatternBindings(chosen.bindings, exec.ctx);
  }
  FuncFlow flow = ExecFuncStmt(chosen.body, exec);
  if (scoped) exec.ctx.PopScope();
  if (labeled) exec.ctx.PopStaticScope(exec.ctx.StmtFrameName(stmt));
  return flow;
}

static FuncFlow ExecFuncRandcase(const Stmt* stmt, const FuncExecCtx& exec) {
  return ExecFuncStmt(SelectRandcaseBranch(stmt, exec.ctx, exec.arena), exec);
}

static FuncFlow ExecFuncRandsequence(const Stmt* stmt,
                                     const FuncExecCtx& exec) {
  ExecRandsequence(stmt, exec.ctx, exec.arena).RunToCompletion();
  return FuncFlow::kNext;
}

FuncFlow ExecFuncStmt(const Stmt* stmt, const FuncExecCtx& exec) {
  if (!stmt) return FuncFlow::kNext;
  NoteStatementExecuted(stmt, exec.ctx);
  switch (stmt->kind) {
    case StmtKind::kReturn:
      if (stmt->expr) ExecFuncReturn(stmt, exec);
      return FuncFlow::kReturn;
    case StmtKind::kBreak:
      return FuncFlow::kBreak;
    case StmtKind::kDisable:
      return ExecFuncDisable(stmt, exec);
    case StmtKind::kContinue:
      return FuncFlow::kContinue;
    case StmtKind::kBlockingAssign:
      ExecFuncBlockingAssign(stmt, exec.ctx, exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kNonblockingAssign:
      ExecNonblockingAssignImpl(stmt, exec.ctx, exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kExprStmt:
      if (!TryExecSystemCallTask(stmt->expr, exec.ctx, exec.arena) &&
          !TryExecMailboxCallInFunction(stmt->expr, exec.ctx, exec.arena) &&
          !TryExecSemaphoreCallInFunction(stmt->expr, exec.ctx, exec.arena)) {
        ExecCallStmtExpr(stmt->expr, exec.ctx, exec.arena);
      }
      return FuncFlow::kNext;
    case StmtKind::kVarDecl:
      ExecFuncVarDecl(stmt, {exec.static_frame, exec.is_static_sub}, exec.ctx,
                      exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kBlockItemDecl:
      ExecBlockItemDeclImpl(stmt, exec.ctx, exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kIf:
      return ExecFuncIf(stmt, exec);
    case StmtKind::kCase:
      return ExecFuncCase(stmt, exec);
    case StmtKind::kBlock:
      return ExecFuncBlock(stmt, exec);
    case StmtKind::kFor:
      return ExecFuncFor(stmt, exec);
    case StmtKind::kForeach:
      return ExecFuncForeach(stmt, exec);
    case StmtKind::kWhile:
      return ExecFuncWhile(stmt, exec);
    case StmtKind::kDoWhile:
      return ExecFuncDoWhile(stmt, exec);
    case StmtKind::kForever:
    case StmtKind::kRepeat:
      return ExecFuncRepeatOrForever(stmt, exec);
    case StmtKind::kEventTrigger:
    case StmtKind::kNbEventTrigger:
      ExecEventTriggerInFunction(stmt, exec.ctx, exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kFork:
      SpawnForkJoinNone(stmt, exec.ctx, exec.arena);
      return FuncFlow::kNext;
    case StmtKind::kAssertImmediate:
    case StmtKind::kAssumeImmediate:
    case StmtKind::kCoverImmediate:
      return ExecFuncImmediateAssert(stmt, exec);
    case StmtKind::kRandcase:
      return ExecFuncRandcase(stmt, exec);
    case StmtKind::kRandsequence:
      return ExecFuncRandsequence(stmt, exec);
    default:
      return FuncFlow::kNext;
  }
}

static void BindReturnStructLayout(const ModuleItem* func, SimContext& ctx) {
  BindNamedLayout(func->name, func->return_type, ctx);
}

static bool ShapeArrayReturnVariable(const ModuleItem* func, SimContext& ctx,
                                     Arena& arena) {
  if (func->return_array_dims.empty()) return false;
  Stmt decl;
  decl.kind = StmtKind::kVarDecl;
  decl.var_name = func->name;
  decl.var_decl_type = func->return_array_elem_type;
  decl.var_unpacked_dims = func->return_array_dims;
  uint32_t width = DeclaredTypeWidth(decl.var_decl_type, ctx);
  CreateDeclAggregate(&decl, width == 0 ? 32 : width, ctx, arena);
  BindNamedLayout(func->name, func->return_array_elem_type, ctx);
  return true;
}

void ExecFunctionBody(const ModuleItem* func, const Expr* call,
                      Variable* ret_var, SimContext& ctx, Arena& arena) {
  VpiActiveFrameScope frame(call);
  FunctionBodyResultScope result_scope(ctx);
  uint32_t ret_width =
      DeclaredTypeWidth(func->return_type, ctx) == 0 ? 0 : ret_var->value.width;
  ShapeStringReturnVariable(func, ret_var, ctx, arena);
  ShapeClassReturnVariable(func, ret_var, ctx, arena);
  StaticLocalFrameScope static_frame(func, ctx, arena);
  std::vector<std::string_view> named_scopes;
  FuncExecCtx exec{ret_var,
                   func->name,
                   static_frame.Name(),
                   ctx,
                   arena,
                   ret_width,
                   func->is_static && !func->is_automatic,
                   &named_scopes};
  BindReturnStructLayout(func, ctx);
  exec.array_return = ShapeArrayReturnVariable(func, ctx, arena);
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, exec) != FuncFlow::kNext) break;
  }
  if (exec.array_return) {
    Expr name;
    name.kind = ExprKind::kIdentifier;
    name.text = func->name;
    RecordReturnedAggregate(&name, ctx, arena);
  }
}

}  // namespace delta
