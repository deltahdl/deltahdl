#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

// §4.8: expression evaluation and net update events may be intermingled within
// the same region. ExecuteRegion drains its queue without dispatching on
// EventKind, so a kEvaluation and a kUpdate scheduled into Active resolve in
// either order; the disjunction encodes the freedom rather than the FIFO
// choice the implementation happens to make.
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

// §4.8 in the Reactive set: the kind-mixing rule is not phrased with an
// Active-only restriction. ExecuteRegion drains every region with the same
// loop, so a kEvaluation and a kUpdate scheduled into Reactive intermingle
// the same way they would in Active.
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

// §4.8 LRM example: assign p = q with initial begin q = 1; #1 q = 0;
// $display(p); end. The simulator may either continue and execute the
// $display task or execute the update for p, followed by the $display task,
// so the displayed value can be either 1 or 0.
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
