#include "simulator/vpi_systf_build.h"

#include <string>
#include <unordered_set>

#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"
#include "simulator/expr_walk.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"

namespace delta {
namespace {

// The build period as it walks the design: the registry it asks, and the calls
// it has already run the routines for. §36.8.2 counts "each instance of a
// system task or system function in the source description", so what a call is
// counted by is the expression the source wrote rather than the elaborated
// module holding it -- Elaborator::ElaborateModule builds a fresh RtlirModule
// per instance and every one of them carries the same parsed call node, so a
// module instantiated twice would otherwise have its compiletf run twice for
// the one call written in it.
struct BuildPeriod {
  VpiContext& vpi;
  // §36.8.2: what a compiletf's call object is built against. `ctx` is where an
  // argument that names a variable finds it, and `arena` is what the call and
  // its arguments are allocated out of.
  SimContext& ctx;
  Arena& arena;
  std::unordered_set<const Expr*> called;
};

// What one system call written in the design asks of the registry while the
// simulation data structure is being built. A name no registration claims is a
// built-in of the tool's own, which has no PLI routines to run and is left to
// §36.3.2's fall-through at execution.
//
// §36.10.2 puts the sizetf routines in a phase of their own -- "the next
// earliest phase is when the sizetf routines are called for the user-defined
// system functions. At this phase, no additional access is permitted" -- so
// that phase is in force while the routine runs and the phase that was standing
// is put back for the compiletf. The order is §36.10.2's too: the sizetf phase
// comes before the cbEndOfCompile callbacks, and a compiletf is what "check[s]
// the correctness of any arguments" (§36.8.2) through the very routines the
// sizetf phase withholds.
void CallBuildPeriodRoutinesForCall(const Expr* call, BuildPeriod& period) {
  if (call == nullptr || call->kind != ExprKind::kSystemCall) return;
  if (!period.called.insert(call).second) return;
  const VpiSystfData* data =
      period.vpi.ResolveSystf(std::string(call->callee).c_str());
  if (data == nullptr) return;

  VpiToolPhase outer = period.vpi.ToolPhase();
  period.vpi.SetToolPhase(VpiToolPhase::kSizetf);
  // §36.8.1: the width is asked for rather than the routine called directly,
  // because "each sizetf routine shall be called at most once" and it is
  // VpiContext::SystfResultSizeBits that remembers what the one run answered.
  if (VpiSystfSizetfIsCalled(*data)) period.vpi.SystfResultSizeBits(*data);
  period.vpi.SetToolPhase(outer);

  // §36.8.2: "This routine is typically used to check the correctness of any
  // arguments passed to the user-defined system task or system function in the
  // SystemVerilog source code", so the call the routine is being run for is
  // stood up around it rather than the routine being called on its own -- the
  // arguments are hung on that call and §36.4 gives an application no other
  // way to them.
  period.vpi.CallCompiletfForSourceCall(*data, call, period.ctx, period.arena);
}

// Every system call written anywhere in `e`. A system call may stand inside
// another expression -- an operand of a sum, an argument of a second call --
// and §36.8.2 has the compiletf called where the name is "encountered", which
// says nothing about the position it was encountered in.
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
  if (mod == nullptr) return;
  for (const auto& proc : mod->processes) {
    CallBuildPeriodRoutinesInStmt(proc.body, period);
  }
  // §10.3: a continuous assignment's right-hand side is an expression the
  // source wrote, so a system call in it was encountered as much as one in a
  // procedure was.
  for (const auto& assign : mod->assigns) {
    CallBuildPeriodRoutinesInExpr(assign.rhs, period);
  }
  // §13.4: a call written in a subroutine's body stands in the source
  // description whether or not any process reaches the subroutine, and the walk
  // over a process's statements does not descend into a declaration.
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
  // A run with nothing registered has no PLI routine to call at any period, so
  // the design is not walked at all rather than walked for names the registry
  // would refuse every one of.
  if (period.vpi.RegisteredSystfs().empty()) return;
  for (auto* top : design->top_modules) {
    CallBuildPeriodRoutinesInModule(top, period);
  }
}

}  // namespace delta
