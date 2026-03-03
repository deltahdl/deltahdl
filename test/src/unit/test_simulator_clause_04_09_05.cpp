// §4.9.5: Switch (transistor) processing

#include <gtest/gtest.h>
#include <cstdint>
#include <string>
#include <vector>
#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

// ===========================================================================
// §4.9.5 Switch (transistor) processing
// ===========================================================================
// ---------------------------------------------------------------------------
// §4.9.5 — Standard unidirectional event processing
// ---------------------------------------------------------------------------
TEST(SimCh4095, UnidirectionalEventProcessing) {
  Arena arena;
  Scheduler sched(arena);
  int input = 5;
  int output = 0;

  // Model: standard gate-level unidirectional flow.
  // Read input, compute result, schedule update — each event independently.
  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() {
    int result = input * 2;  // Read input, compute result.
    auto* update = sched.GetEventPool().Acquire();
    update->kind = EventKind::kUpdate;
    update->callback = [&, result]() { output = result; };  // Schedule update.
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update);
  };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  sched.Run();
  EXPECT_EQ(output, 10);
}

}  // namespace
