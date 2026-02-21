#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"

using namespace delta;

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
  auto* ev = sched.GetEventPool().Acquire();
  ev->callback = [&executed]() { executed = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev);
  EXPECT_TRUE(sched.HasEvents());
  sched.Run();
  EXPECT_TRUE(executed);
}

// --- EventPool tests ---

TEST(EventPool, AcquireCreatesNew) {
  Arena arena;
  EventPool pool(arena);
  Event* ev = pool.Acquire();
  ASSERT_NE(ev, nullptr);
  EXPECT_EQ(ev->kind, EventKind::kEvaluation);
  EXPECT_EQ(ev->target, nullptr);
  EXPECT_EQ(ev->next, nullptr);
}

TEST(EventPool, ReleaseAndReuse) {
  Arena arena;
  EventPool pool(arena);
  Event* ev = pool.Acquire();
  ev->callback = []() {};
  ev->target = reinterpret_cast<void*>(0x1234);
  pool.Release(ev);
  EXPECT_EQ(pool.FreeCount(), 1);

  Event* reused = pool.Acquire();
  EXPECT_EQ(reused, ev);               // Same pointer returned
  EXPECT_EQ(reused->target, nullptr);  // Fields cleared
  EXPECT_EQ(pool.FreeCount(), 0);
}

TEST(EventPool, FreeCount) {
  Arena arena;
  EventPool pool(arena);
  EXPECT_EQ(pool.FreeCount(), 0);

  Event* ev1 = pool.Acquire();
  Event* ev2 = pool.Acquire();
  pool.Release(ev1);
  pool.Release(ev2);
  EXPECT_EQ(pool.FreeCount(), 2);

  pool.Acquire();
  EXPECT_EQ(pool.FreeCount(), 1);
}

TEST(Scheduler, EventPoolIntegration) {
  Arena arena;
  Scheduler sched(arena);
  auto& pool = sched.GetEventPool();
  EXPECT_EQ(pool.FreeCount(), 0);

  auto* ev = pool.Acquire();
  bool ran = false;
  ev->callback = [&ran]() { ran = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev);

  sched.Run();
  EXPECT_TRUE(ran);
  // After execution, event should be recycled into the pool.
  EXPECT_EQ(pool.FreeCount(), 1);
}
