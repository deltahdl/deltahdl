#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_sampling.h"

namespace delta {

namespace {

// §16.9.3's four value change functions.
bool IsValueChangeFunction(std::string_view name) {
  return name == "$rose" || name == "$fell" || name == "$stable" ||
         name == "$changed";
}

// §16.9.3 (printed pages 415 and 417): a value change function given a
// clocking event of its own compares the sampled value of its argument now
// with the one at the most recent strictly prior time step in which that
// event occurred, whatever clock or procedure the call stands in. This
// process records that sample at every tick of the event, as the call site's
// history, which the call reads (EvalPastOrValueChange in
// eval_systask_verif.cpp) and does not write.
SimCoroutine MakeSampledClockMonitor(const Expr* site, SimContext& ctx,
                                     Arena& arena) {
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, *site->sampled_clock, arena};
    Logic4Vec value = EvalSampledArg(site->args[0], ctx, arena);
    ctx.AssertionSamples().RecordTick(
        SampleSite{site, 0, ctx.CurrentTime().ticks}, value, 1, arena);
  }
}

}  // namespace

void Lowerer::LowerSampledClockMonitors(const Stmt* body) {
  ForEachStmtReadExpr(body, [this](const Expr* e) {
    ForEachSubExpr(e, [this](const Expr* sub) {
      if (sub->kind != ExprKind::kSystemCall || sub->sampled_clock == nullptr ||
          sub->args.empty() || sub->args[0] == nullptr ||
          !IsValueChangeFunction(sub->callee)) {
        return;
      }
      auto* p = arena_.Create<Process>();
      p->kind = ProcessKind::kAlways;
      p->id = next_id_++;
      p->home_region = Region::kActive;
      p->inst_prefix = inst_prefix_;
      p->rng_seed = ctx_.DrawSeedForChild();
      p->coro = MakeSampledClockMonitor(sub, ctx_, arena_).Release();
      ScheduleProcess(p, ctx_);
    });
  });
}

}  // namespace delta
