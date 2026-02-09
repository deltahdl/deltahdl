#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/process.h"
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

TEST(Scheduler, TimeOrdering) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev1 = sched.GetEventPool().Acquire();
  ev1->callback = [&order]() { order.push_back(1); };

  auto* ev2 = sched.GetEventPool().Acquire();
  ev2->callback = [&order]() { order.push_back(2); };

  sched.ScheduleEvent({10}, Region::kActive, ev2);
  sched.ScheduleEvent({5}, Region::kActive, ev1);

  sched.Run();
  ASSERT_EQ(order.size(), 2);
  EXPECT_EQ(order[0], 1);  // time 5 first
  EXPECT_EQ(order[1], 2);  // time 10 second
}

TEST(Scheduler, RegionOrderingWithinTimeSlot) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  auto* ev_active = sched.GetEventPool().Acquire();
  ev_active->callback = [&order]() { order.push_back(1); };

  auto* ev_nba = sched.GetEventPool().Acquire();
  ev_nba->callback = [&order]() { order.push_back(2); };

  // Schedule NBA before Active, but Active should execute first
  sched.ScheduleEvent({0}, Region::kNBA, ev_nba);
  sched.ScheduleEvent({0}, Region::kActive, ev_active);

  sched.Run();
  ASSERT_EQ(order.size(), 2);
  EXPECT_EQ(order[0], 1);  // Active first
  EXPECT_EQ(order[1], 2);  // NBA second
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

// --- Gap 1: Process reactive context tracking ---

TEST(Scheduler, ReactiveContextTracking) {
  Process proc;
  // Default should be non-reactive (active context).
  EXPECT_FALSE(proc.is_reactive);

  // Setting to reactive context.
  proc.is_reactive = true;
  EXPECT_TRUE(proc.is_reactive);
}

// --- Gap 2: Reactive region scheduling for #0 delays ---

TEST(Scheduler, ReactiveDelayScheduling) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  // A #0 delay in active context should go to kInactive.
  auto* ev_inactive = sched.GetEventPool().Acquire();
  ev_inactive->callback = [&order]() { order.push_back(1); };
  sched.ScheduleEvent({0}, Region::kInactive, ev_inactive);

  // A #0 delay in reactive context should go to kReInactive.
  auto* ev_reinactive = sched.GetEventPool().Acquire();
  ev_reinactive->callback = [&order]() { order.push_back(2); };
  sched.ScheduleEvent({0}, Region::kReInactive, ev_reinactive);

  sched.Run();
  ASSERT_EQ(order.size(), 2);
  // Inactive (active set) runs before ReInactive (reactive set).
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

// --- Gap 3: Reactive region scheduling for NBA ---

TEST(Scheduler, ReactiveNBAScheduling) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  // NBA in active context goes to kNBA.
  auto* ev_nba = sched.GetEventPool().Acquire();
  ev_nba->callback = [&order]() { order.push_back(1); };
  sched.ScheduleEvent({0}, Region::kNBA, ev_nba);

  // NBA in reactive context goes to kReNBA.
  auto* ev_renba = sched.GetEventPool().Acquire();
  ev_renba->callback = [&order]() { order.push_back(2); };
  sched.ScheduleEvent({0}, Region::kReNBA, ev_renba);

  sched.Run();
  ASSERT_EQ(order.size(), 2);
  // kNBA (active set) runs before kReNBA (reactive set).
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}

// --- Gap 4: Update event propagation ---

TEST(Scheduler, UpdateEventPropagation) {
  Arena arena;
  Scheduler sched(arena);
  bool update_ran = false;
  bool eval_ran = false;

  // Schedule an update event in Active region.
  auto* ev_update = sched.GetEventPool().Acquire();
  ev_update->kind = EventKind::kUpdate;
  ev_update->callback = [&update_ran]() { update_ran = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev_update);

  // Schedule an evaluation event in Active region.
  auto* ev_eval = sched.GetEventPool().Acquire();
  ev_eval->kind = EventKind::kEvaluation;
  ev_eval->callback = [&eval_ran]() { eval_ran = true; };
  sched.ScheduleEvent({0}, Region::kActive, ev_eval);

  sched.Run();
  // Both update and evaluation events should execute.
  EXPECT_TRUE(update_ran);
  EXPECT_TRUE(eval_ran);
}

// --- Gap 5: Preponed region scheduling ---

TEST(Scheduler, PreponeScheduling) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<int> order;

  // Schedule an event in Preponed region of time 5.
  auto* ev_preponed = sched.GetEventPool().Acquire();
  ev_preponed->callback = [&order]() { order.push_back(1); };
  sched.ScheduleEvent({5}, Region::kPreponed, ev_preponed);

  // Schedule an event in Active region of time 5.
  auto* ev_active = sched.GetEventPool().Acquire();
  ev_active->callback = [&order]() { order.push_back(2); };
  sched.ScheduleEvent({5}, Region::kActive, ev_active);

  sched.Run();
  ASSERT_EQ(order.size(), 2);
  // Preponed runs before Active within the same time slot.
  EXPECT_EQ(order[0], 1);
  EXPECT_EQ(order[1], 2);
}
