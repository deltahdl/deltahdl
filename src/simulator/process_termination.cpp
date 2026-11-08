#include "simulator/process_termination.h"

#include "common/types.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

static bool IsProcessKillable(const Process& proc) {
  return proc.sv_state != ProcessState::kFinished &&
         proc.sv_state != ProcessState::kKilled;
}

void TerminateProcess(Process& proc, SimContext& ctx) {
  if (!IsProcessKillable(proc)) return;
  proc.Kill();
  GetGlobalVpiContext().NoteThreadEnded(&proc);
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  Process* released = &proc;
  event->callback = [released]() { released->ReleaseFromFork(); };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive, event);
}

}  // namespace delta
