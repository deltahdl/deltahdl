#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/scheduler.h"

using namespace delta;

namespace {

// Schedules the shared "q = 0" Active-region evaluation that, when it fires,
// enqueues the enabled net update (p = q) ahead of the continuation read
// (display_result = p) into the same Active region. Used by the tests whose
// intermingling places the update before the read. The captured references
// (q, p, display_result) and the trigger time are the only varying parts.
void ScheduleAssignThenUpdateBeforeRead(Scheduler& sched, int& q, int& p,
                                        int& display_result, SimTime when) {
  auto* assign_zero = sched.GetEventPool().Acquire();
  assign_zero->kind = EventKind::kEvaluation;
  assign_zero->callback = [&sched, &q, &p, &display_result]() {
    q = 0;

    auto* update_p = sched.GetEventPool().Acquire();
    update_p->kind = EventKind::kUpdate;
    update_p->callback = [&p, &q]() { p = q; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);

    auto* display = sched.GetEventPool().Acquire();
    display->kind = EventKind::kEvaluation;
    display->callback = [&display_result, &p]() { display_result = p; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, display);
  };
  sched.ScheduleEvent(when, Region::kActive, assign_zero);
}

}  // namespace

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

  ScheduleAssignThenUpdateBeforeRead(sched, q, p, display_result, {1});

  sched.Run();

  EXPECT_TRUE(display_result == 0 || display_result == 1);
}

// §4.8 spells out the two legal resolutions of the race explicitly: the read
// may run before the enabled net update (seeing the old value) or after it
// (seeing the new value). The next two tests pin each permitted outcome to a
// specific intermingling order and confirm the production scheduler actually
// produces it, drives the net update either way, and never drops it.

// Read enqueued ahead of the update it enabled: the scheduler drains the
// Active queue in arrival order, so the read observes the pre-update value
// while the enabled update still completes afterward.
TEST(RaceConditionSim, ReadObservesOldValueWhenScheduledBeforeEnabledUpdate) {
  Arena arena;
  Scheduler sched(arena);
  int q = 1;
  int p = 1;  // continuous assignment p = q already propagated q's prior value
  int display_result = -1;

  auto* assign_zero = sched.GetEventPool().Acquire();
  assign_zero->kind = EventKind::kEvaluation;
  assign_zero->callback = [&]() {
    q = 0;

    auto* display = sched.GetEventPool().Acquire();
    display->kind = EventKind::kEvaluation;
    display->callback = [&]() { display_result = p; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, display);

    auto* update_p = sched.GetEventPool().Acquire();
    update_p->kind = EventKind::kUpdate;
    update_p->callback = [&]() { p = q; };
    sched.ScheduleEvent(sched.CurrentTime(), Region::kActive, update_p);
  };
  sched.ScheduleEvent({1}, Region::kActive, assign_zero);

  sched.Run();

  EXPECT_EQ(display_result, 1);  // read saw the value before the update applied
  EXPECT_EQ(p, 0);               // the enabled update still ran afterward
}

// Update enqueued ahead of the read: the same Active-region drain applies the
// net update first, so the read observes the post-update value. Together with
// the previous test this shows the real scheduler yields either legal result
// depending solely on how the events intermingle.
TEST(RaceConditionSim, ReadObservesNewValueWhenEnabledUpdatePrecedesIt) {
  Arena arena;
  Scheduler sched(arena);
  int q = 1;
  int p = 1;
  int display_result = -1;

  ScheduleAssignThenUpdateBeforeRead(sched, q, p, display_result, {1});

  sched.Run();

  EXPECT_EQ(display_result, 0);  // read saw the value after the update applied
  EXPECT_EQ(p, 0);
}
