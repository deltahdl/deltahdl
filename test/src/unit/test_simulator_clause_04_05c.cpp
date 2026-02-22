// §4.5: SystemVerilog simulation reference algorithm

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"
#include <gtest/gtest.h>

using namespace delta;

namespace {

TEST(Scheduler, InitialState) {
  Arena arena;
  Scheduler sched(arena);
  EXPECT_FALSE(sched.HasEvents());
  EXPECT_EQ(sched.CurrentTime().ticks, 0);
}

TEST(Scheduler, ScheduleAndRunSingleEvent) {
  Arena arena;
  Scheduler sched(arena);
  bool executed = false;
  auto *ev = sched.GetEventPool().Acquire();
  ev->callback = [&executed]() { executed = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev);
  EXPECT_TRUE(sched.HasEvents());
  sched.Run();
  EXPECT_TRUE(executed);
}

} // namespace
