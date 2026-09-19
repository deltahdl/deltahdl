// §13.3: a task enabled through an object handle, `h.t(...)`, run as a
// coroutine so that a delay or event control in its body suspends the enabling
// process and control comes back to it when the task has completed, at
// whatever time that is. ExecInlineTaskCall in stmt_exec.cpp reaches this once
// SetupInstanceTaskCall has resolved the call and pushed its frame.

#include "common/arena.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_instance_task.h"
#include "simulator/exec_task.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"

namespace delta {

ExecTask ExecInstanceTaskCall(const InstanceMethodInfo& call, const Expr* expr,
                              SimContext& ctx, Arena& arena) {
  StmtResult outcome = StmtResult::kDone;
  for (auto* s : call.method->func_body_stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    // §13.3: a return statement ends the task; a disable of an enclosing
    // block (§9.6.2) ends it too and goes on to the enabling process.
    if (result == StmtResult::kReturn) break;
    if (result == StmtResult::kDisable) {
      outcome = result;
      break;
    }
  }
  TeardownInstanceTaskCall(call, expr, ctx, arena);
  co_return outcome;
}

}  // namespace delta
