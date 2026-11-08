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

static const s_vpi_systf_data* ResolveSystfTask(const Expr* expr) {
  const s_vpi_systf_data* data =
      GetGlobalVpiContext().ResolveSystf(std::string(expr->callee).c_str());
  return data != nullptr && data->type == kVpiSysTask ? data : nullptr;
}

bool TryExecSystemCallTask(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->kind != ExprKind::kSystemCall) return false;

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

  if (expr->callee == "$stacktrace") {
    ctx.Out() << BuildStackTraceReport(ctx) << "\n";
    return true;
  }

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
