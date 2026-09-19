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
#include "simulator/statement_assign.h"
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

// §10.4 gives every procedure one set of assignments, and a class method adds
// the targets §8.10 and §8.11 give it over its own class: a property by its
// bare name, `this.x`, `super.x`, a `new` resolved against a property. The
// function interpreter answers those in ExecFuncBlockingAssign, and a task body
// run here as a coroutine is inside the same method, so its immediate
// assignments go the same way; without this, `command = 8'hFF;` in a class
// task wrote a local of the pushed scope and the property kept 0.
StmtResult ExecImmediateBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                       Arena& arena) {
  if (ctx.CurrentThis() != nullptr || ctx.CurrentMethodClass() != nullptr) {
    ExecFuncBlockingAssign(stmt, ctx, arena);
    return StmtResult::kDone;
  }
  return ExecBlockingAssignImpl(stmt, ctx, arena);
}

}  // namespace delta
