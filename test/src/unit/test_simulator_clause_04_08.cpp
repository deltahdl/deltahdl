#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

TEST(RaceConditionSim, EvalAndUpdateEventsIntermingleInActive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() { order.push_back("eval"); };
  sched.ScheduleEvent({0}, Region::kActive, eval);

  auto* update = sched.GetEventPool().Acquire();
  update->kind = EventKind::kUpdate;
  update->callback = [&]() { order.push_back("update"); };
  sched.ScheduleEvent({0}, Region::kActive, update);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);

  EXPECT_TRUE((order[0] == "eval" && order[1] == "update") ||
              (order[0] == "update" && order[1] == "eval"));
}

TEST(RaceConditionSim, EvalAndUpdateEventsIntermingleInReactive) {
  Arena arena;
  Scheduler sched(arena);
  std::vector<std::string> order;

  auto* eval = sched.GetEventPool().Acquire();
  eval->kind = EventKind::kEvaluation;
  eval->callback = [&]() { order.push_back("eval"); };
  sched.ScheduleEvent({0}, Region::kReactive, eval);

  auto* update = sched.GetEventPool().Acquire();
  update->kind = EventKind::kUpdate;
  update->callback = [&]() { order.push_back("update"); };
  sched.ScheduleEvent({0}, Region::kReactive, update);

  sched.Run();
  ASSERT_EQ(order.size(), 2u);

  EXPECT_TRUE((order[0] == "eval" && order[1] == "update") ||
              (order[0] == "update" && order[1] == "eval"));
}

TEST(RaceConditionSim, ProcessContinuationRacesEnabledNetUpdate) {
  Arena arena;
  Scheduler sched(arena);
  int q = 0;
  int p = 0;
  int display_result = -1;

  auto* init_q = sched.GetEventPool().Acquire();
  init_q->kind = EventKind::kEvaluation;
  init_q->callback = [&]() {
    q = 1;

    auto* update_p = sched.GetEventPool().Acquire();
    update_p->kind = EventKind::kUpdate;
    update_p->callback = [&]() { p = q; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);
  };
  sched.ScheduleEvent({0}, Region::kActive, init_q);

  auto* assign_zero = sched.GetEventPool().Acquire();
  assign_zero->kind = EventKind::kEvaluation;
  assign_zero->callback = [&]() {
    q = 0;

    auto* update_p = sched.GetEventPool().Acquire();
    update_p->kind = EventKind::kUpdate;
    update_p->callback = [&]() { p = q; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);

    auto* display = sched.GetEventPool().Acquire();
    display->kind = EventKind::kEvaluation;
    display->callback = [&]() { display_result = p; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, display);
  };
  sched.ScheduleEvent({1}, Region::kActive, assign_zero);

  sched.Run();

  EXPECT_TRUE(display_result == 0 || display_result == 1);
}
