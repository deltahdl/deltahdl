#include <string>

#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {

// §36.5: the registration a system call name resolves to, when it is one whose
// type is vpiSysTask. The clause has the type decide the way the source code
// calls an application, and a task is the type that may stand wherever a void
// function may -- which §13.4.1 makes a statement and not an operand, since
// only a call of a non-void function may serve as an expression. So this is the
// position a task-typed registration is called from, and the expression
// evaluator refuses the same name there.
static const s_vpi_systf_data* ResolveSystfTask(const Expr* expr) {
  const s_vpi_systf_data* data =
      GetGlobalVpiContext().ResolveSystf(std::string(expr->callee).c_str());
  return data != nullptr && data->type == kVpiSysTask ? data : nullptr;
}

bool TryExecSystemCallTask(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (!expr || expr->kind != ExprKind::kSystemCall) return false;

  // $cast invoked as a task: the evaluation performs the assignment when the
  // cast is valid and leaves the destination untouched otherwise. Unlike the
  // function form (which simply reports 0), the task form signals an invalid
  // assignment with a run-time error.
  if (expr->callee == "$cast") {
    auto result = EvalExpr(expr, ctx, arena);
    if (result.ToUint64() == 0) {
      ctx.GetDiag().Error(expr->range.start,
                          "$cast task could not assign the source expression "
                          "to the destination; assignment is invalid",
                          Subclause("6.24.2"));
    }
    return true;
  }

  // §20.17.2: invoked as a task, $stacktrace displays the call stack of the
  // context calling it, up to the top-level process. The function form, which
  // instead returns the same text as a string, is evaluated as an expression.
  if (expr->callee == "$stacktrace") {
    ctx.Out() << BuildStackTraceReport(ctx) << "\n";
    return true;
  }

  // §36.5: a user-defined system task is called from here, the one position it
  // has, and its result is dropped rather than returned -- the clause lets a
  // task read and change its arguments but gives it no value to yield. Reaching
  // the application from this position rather than from the expression
  // evaluator is what lets that evaluator report the same name as a task
  // standing where a value is wanted; a dispatch that served both positions
  // could tell them apart nowhere.
  const s_vpi_systf_data* task = ResolveSystfTask(expr);
  if (task != nullptr) {
    Logic4Vec dropped;
    GetGlobalVpiContext().CallRegisteredSystf(task->tfname, expr, ctx, dropped,
                                              arena);
    return true;
  }
  return false;
}

bool SystemCallNamesARegisteredTask(const Expr* expr) {
  return ResolveSystfTask(expr) != nullptr;
}

}  // namespace delta
