#include <utility>

#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"

namespace delta {

void TriggerEvent(Variable* var, SimContext& ctx) {
  TriggerEventIn(var, ctx,
                 ctx.IsReactiveContext() ? Region::kReactive : Region::kActive);
}

void TriggerEventIn(Variable* var, SimContext& ctx, Region region) {
  var->triggered_ticks = ctx.CurrentTime().ticks;

  auto pending = std::move(var->watchers);
  var->watchers.clear();
  auto& sched = ctx.GetScheduler();
  for (auto& cb : pending) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [var, cb = std::move(cb)]() mutable {
      if (!cb()) var->AddWatcher(std::move(cb));
    };
    sched.ScheduleEvent(ctx.CurrentTime(), region, event);
  }
}

}  // namespace delta
