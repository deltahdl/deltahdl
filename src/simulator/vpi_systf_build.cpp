#include "simulator/vpi_systf_build.h"

#include <string>
#include <unordered_set>

#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "simulator/expr_walk.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct BuildPeriod {
  VpiContext& vpi;
  SimContext& ctx;
  Arena& arena;
  std::unordered_set<const Expr*> called;
};

void CallBuildPeriodRoutinesForCall(const Expr* call, BuildPeriod& period) {
  if (call->kind != ExprKind::kSystemCall) return;
  if (!period.called.insert(call).second) return;
  const s_vpi_systf_data* data =
      period.vpi.ResolveSystf(std::string(call->callee).c_str());
  if (data == nullptr) return;

  VpiToolPhase outer = period.vpi.ToolPhase();
  period.vpi.SetToolPhase(VpiToolPhase::kSizetf);
  if (VpiSystfSizetfIsCalled(*data)) period.vpi.SystfResultSizeBits(*data);
  period.vpi.SetToolPhase(outer);

  period.vpi.CallCompiletfForSourceCall(*data, call, period.ctx, period.arena);
}

void CallBuildPeriodRoutinesInExpr(const Expr* e, BuildPeriod& period) {
  ForEachSubExpr(e, [&period](const Expr* sub) {
    CallBuildPeriodRoutinesForCall(sub, period);
  });
}

void CallBuildPeriodRoutinesInStmt(const Stmt* stmt, BuildPeriod& period) {
  ForEachStmtReadExpr(stmt, [&period](const Expr* e) {
    CallBuildPeriodRoutinesInExpr(e, period);
  });
}

void CallBuildPeriodRoutinesInModule(const RtlirModule* mod,
                                     BuildPeriod& period) {
  for (const auto& proc : mod->processes) {
    CallBuildPeriodRoutinesInStmt(proc.body, period);
  }
  for (const auto& assign : mod->assigns) {
    CallBuildPeriodRoutinesInExpr(assign.rhs, period);
  }
  for (const auto& var : mod->variables) {
    CallBuildPeriodRoutinesInExpr(var.init_expr, period);
  }
  for (const auto* func : mod->function_decls) {
    for (const auto* stmt : func->func_body_stmts) {
      CallBuildPeriodRoutinesInStmt(stmt, period);
    }
  }
  for (const auto& child : mod->children) {
    CallBuildPeriodRoutinesInModule(child.resolved, period);
  }
}

}  // namespace

void CallBuildPeriodSystfRoutines(const RtlirDesign* design, SimContext& ctx,
                                  Arena& arena) {
  BuildPeriod period{GetGlobalVpiContext(), ctx, arena, {}};
  if (period.vpi.RegisteredSystfs().empty()) return;
  for (auto* top : design->top_modules) {
    CallBuildPeriodRoutinesInModule(top, period);
  }
}

}  // namespace delta
