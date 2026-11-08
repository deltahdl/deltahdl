#include "common/arena.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_instance_task.h"
#include "simulator/exec_task.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/vpi_design_attach.h"

namespace delta {

ExecTask ExecInstanceTaskCall(const InstanceMethodInfo& call, const Expr* expr,
                              SimContext& ctx, Arena& arena) {
  VpiActiveFrameScope frame(expr);
  StmtResult outcome = StmtResult::kDone;
  for (auto* s : call.method->func_body_stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kReturn) break;
    if (result == StmtResult::kDisable) {
      outcome = result;
      break;
    }
    if (ctx.StopRequested()) break;
  }
  TeardownInstanceTaskCall(call, expr, ctx, arena);
  co_return outcome;
}

StmtResult ExecImmediateBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                       Arena& arena) {
  if (ctx.CurrentThis() != nullptr || ctx.CurrentMethodClass() != nullptr) {
    ExecFuncBlockingAssign(stmt, ctx, arena);
    return StmtResult::kDone;
  }
  return ExecBlockingAssignImpl(stmt, ctx, arena);
}

}  // namespace delta
