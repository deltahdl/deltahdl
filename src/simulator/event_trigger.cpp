#include <utility>

#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/variable.h"

namespace delta {

void TriggerEvent(Variable* var, SimContext& ctx) {
  // §15.5.3: the event itself records the step, which a class's event
  // property, found by no name, is read by (TryClassEventTriggered).
  var->triggered_ticks = ctx.CurrentTime().ticks;

  auto pending = std::move(var->watchers);
  var->watchers.clear();
  auto& sched = ctx.GetScheduler();
  auto region = ctx.IsReactiveContext() ? Region::kReactive : Region::kActive;
  // A watcher answers false when this trigger does not wake it -- its process
  // is suspended (§9.7) or its `iff` does not hold (§9.4.2.3) -- and it stays
  // armed for the next trigger, as Variable::NotifyWatchers keeps it.
  for (auto& cb : pending) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [var, cb = std::move(cb)]() mutable {
      if (!cb()) var->AddWatcher(std::move(cb));
    };
    sched.ScheduleEvent(ctx.CurrentTime(), region, event);
  }
}

}  // namespace delta
