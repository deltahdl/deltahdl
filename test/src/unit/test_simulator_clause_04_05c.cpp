// Non-LRM tests

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

TEST(Scheduler, ScheduleAndRunSingleEvent) {
  Arena arena;
  Scheduler sched(arena);
  bool executed = false;
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&executed]() { executed = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev);
  EXPECT_TRUE(sched.HasEvents());
  sched.Run();
  EXPECT_TRUE(executed);
}

}  // namespace
